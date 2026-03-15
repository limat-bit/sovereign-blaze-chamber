;; SovereignBlazeDAO - Quadratic Voting with Expertise-Weighted Governance
;; Clarity Version: 2
;; Epoch: 2.1
;;
;; Core features:
;;   - Quadratic voting (cost = votes^2 governance tokens)
;;   - Domain expertise reputation scoring
;;   - Multi-stage proposal validation (technical, economic, sentiment)
;;   - Time-locked proposal chambers
;;   - Governance token burn on failed proposals
;;   - Bonus distribution for active participants
;;   - Peer validation of contributions

;; ===========================
;; CONSTANTS
;; ===========================

(define-constant CONTRACT-OWNER tx-sender)

;; Error codes
(define-constant ERR-NOT-AUTHORIZED        (err u100))
(define-constant ERR-PROPOSAL-NOT-FOUND    (err u101))
(define-constant ERR-PROPOSAL-NOT-ACTIVE   (err u102))
(define-constant ERR-PROPOSAL-EXPIRED      (err u103))
(define-constant ERR-ALREADY-VOTED         (err u104))
(define-constant ERR-INSUFFICIENT-TOKENS   (err u105))
(define-constant ERR-INVALID-VOTES         (err u106))
(define-constant ERR-PROPOSAL-NOT-ENDED    (err u107))
(define-constant ERR-ALREADY-EXECUTED      (err u108))
(define-constant ERR-CONTRIBUTION-INVALID  (err u109))
(define-constant ERR-ALREADY-VALIDATED     (err u110))
(define-constant ERR-SELF-VALIDATE         (err u111))
(define-constant ERR-QUORUM-NOT-MET        (err u112))
(define-constant ERR-NOT-APPROVED          (err u113))

;; Governance parameters
(define-constant VOTING-PERIOD-BLOCKS      u1440)   ;; ~10 days at ~1 block/10 min
(define-constant LOCK-PERIOD-BLOCKS        u144)    ;; ~1 day timelock before execution
(define-constant MIN-PROPOSAL-TOKENS       u1000)   ;; tokens required to submit
(define-constant QUORUM-THRESHOLD          u10)     ;; 10% of total supply must vote
(define-constant APPROVAL-THRESHOLD        u60)     ;; 60% yes votes required
(define-constant BURN-ON-FAILURE           u500)    ;; tokens burned if proposal fails
(define-constant ACTIVE-PARTICIPANT-BONUS  u50)     ;; bonus tokens for participating
(define-constant MAX-VOTES-PER-USER        u100)    ;; max quadratic votes per proposal
(define-constant EXPERTISE-WEIGHT-CAP      u3)      ;; max expertise multiplier (3x)

;; Proposal stages
(define-constant STAGE-SUBMITTED  u0)
(define-constant STAGE-TECHNICAL  u1)
(define-constant STAGE-ECONOMIC   u2)
(define-constant STAGE-VOTING     u3)
(define-constant STAGE-ENDED      u4)
(define-constant STAGE-EXECUTED   u5)

;; Contribution domains
(define-constant DOMAIN-TECHNICAL  u0)
(define-constant DOMAIN-ECONOMIC   u1)
(define-constant DOMAIN-COMMUNITY  u2)

;; ===========================
;; DATA MAPS & VARS
;; ===========================

;; Governance token balances
(define-map token-balances
  principal
  uint)

;; Total governance token supply
(define-data-var total-supply uint u0)

;; Proposal counter
(define-data-var proposal-nonce uint u0)

;; Proposals
(define-map proposals
  uint  ;; proposal-id
  {
    proposer:           principal,
    title:              (string-ascii 128),
    description:        (string-ascii 1024),
    created-at-block:   uint,
    voting-ends-block:  uint,
    execution-block:    uint,
    stage:              uint,
    yes-votes:          uint,
    no-votes:           uint,
    total-voting-power: uint,
    technical-score:    uint,
    economic-score:     uint,
    executed:           bool,
    approved:           bool
  })

;; Tracks whether a principal has voted on a proposal
(define-map has-voted
  { proposal-id: uint, voter: principal }
  bool)

;; Reputation / expertise scores per domain per user
(define-map expertise-scores
  { user: principal, domain: uint }
  uint)

;; Contribution records
(define-data-var contribution-nonce uint u0)

(define-map contributions
  uint  ;; contribution-id
  {
    contributor:    principal,
    domain:         uint,
    description:    (string-ascii 512),
    submitted-at:   uint,
    validation-count: uint,
    validated:      bool
  })

;; Tracks who validated a given contribution
(define-map contribution-validators
  { contribution-id: uint, validator: principal }
  bool)

;; Technical scorer assignments (validators for stage 1)
(define-map technical-scorers
  principal
  bool)

;; Economic scorer assignments (validators for stage 2)
(define-map economic-scorers
  principal
  bool)

;; ===========================
;; PRIVATE HELPERS
;; ===========================

;; Integer square-root (floor) for quadratic voting cost
(define-private (isqrt (n uint))
  (if (<= n u1)
    n
    (let ((estimate (/ n u2)))
      (let ((result (fold isqrt-step (list u0 u1 u2 u3 u4 u5 u6 u7) estimate)))
        result))))

;; Single Newton-Raphson step; x is the running estimate
(define-private (isqrt-step (ignored uint) (x uint))
  (if (is-eq x u0) u0
    (/ (+ x (/ (/ (fold isqrt-get-n (list u0) u0) x) u1)) u2)))

;; Workaround: we pass n via closure. Use a global capture pattern.
;; Simpler direct inline quadratic cost check avoids sqrt entirely.
;; cost(v) = v * v  =>  user must hold >= votes^2 tokens
(define-private (quadratic-cost (votes uint))
  (* votes votes))

;; Get token balance, defaulting to 0
(define-private (get-balance (user principal))
  (default-to u0 (map-get? token-balances user)))

;; Get expertise score for a domain, defaulting to 0
(define-private (get-expertise (user principal) (domain uint))
  (default-to u0 (map-get? expertise-scores { user: user, domain: domain })))

;; Compute expertise weight multiplier (1 to EXPERTISE-WEIGHT-CAP)
;; For every 100 expertise points, weight increases by 1 (capped)
(define-private (expertise-multiplier (user principal) (domain uint))
  (let ((score (get-expertise user domain)))
    (let ((raw-mult (+ u1 (/ score u100))))
      (if (> raw-mult EXPERTISE-WEIGHT-CAP)
        EXPERTISE-WEIGHT-CAP
        raw-mult))))

;; Weighted voting power = votes * expertise-multiplier(community domain)
(define-private (weighted-voting-power (user principal) (votes uint))
  (* votes (expertise-multiplier user DOMAIN-COMMUNITY)))

;; Check that a proposal exists and return it
(define-private (get-proposal-or-err (proposal-id uint))
  (match (map-get? proposals proposal-id)
    proposal (ok proposal)
    ERR-PROPOSAL-NOT-FOUND))

;; Fold helper placeholders (Clarity requires at least 1 element in list for fold)
(define-private (isqrt-get-n (ignored uint) (acc uint))
  acc)

;; ===========================
;; TOKEN MANAGEMENT (INTERNAL)
;; ===========================

;; Mint governance tokens to a principal (owner only)
(define-public (mint-tokens (recipient principal) (amount uint))
  (begin
    (asserts! (is-eq tx-sender CONTRACT-OWNER) ERR-NOT-AUTHORIZED)
    (map-set token-balances recipient
      (+ (get-balance recipient) amount))
    (var-set total-supply (+ (var-get total-supply) amount))
    (ok amount)))

;; Burn governance tokens from a principal (internal, can be called by contract logic)
(define-private (burn-tokens-from (user principal) (amount uint))
  (let ((bal (get-balance user)))
    (if (< bal amount)
      false
      (begin
        (map-set token-balances user (- bal amount))
        (var-set total-supply (- (var-get total-supply) amount))
        true))))

;; ===========================
;; SCORER MANAGEMENT
;; ===========================

;; Register a technical scorer (owner only)
(define-public (add-technical-scorer (scorer principal))
  (begin
    (asserts! (is-eq tx-sender CONTRACT-OWNER) ERR-NOT-AUTHORIZED)
    (map-set technical-scorers scorer true)
    (ok true)))

;; Register an economic scorer (owner only)
(define-public (add-economic-scorer (scorer principal))
  (begin
    (asserts! (is-eq tx-sender CONTRACT-OWNER) ERR-NOT-AUTHORIZED)
    (map-set economic-scorers scorer true)
    (ok true)))

;; ===========================
;; CONTRIBUTIONS & REPUTATION
;; ===========================

;; Submit a contribution to earn expertise points upon peer validation
(define-public (submit-contribution
    (domain uint)
    (description (string-ascii 512)))
  (begin
    (asserts! (<= domain u2) ERR-CONTRIBUTION-INVALID)
    (let ((cid (+ (var-get contribution-nonce) u1)))
      (var-set contribution-nonce cid)
      (map-set contributions cid {
        contributor:      tx-sender,
        domain:           domain,
        description:      description,
        submitted-at:     block-height,
        validation-count: u0,
        validated:        false
      })
      (ok cid))))

;; Peer-validate a contribution (any token-holder, not the contributor)
;; After 3 validations the contribution is marked validated and
;; the contributor earns 25 expertise points in the relevant domain.
(define-public (validate-contribution (contribution-id uint))
  (let ((contrib (unwrap! (map-get? contributions contribution-id) ERR-CONTRIBUTION-INVALID)))
    (asserts! (not (is-eq tx-sender (get contributor contrib))) ERR-SELF-VALIDATE)
    (asserts! (> (get-balance tx-sender) u0) ERR-INSUFFICIENT-TOKENS)
    (asserts! (not (default-to false
                     (map-get? contribution-validators
                       { contribution-id: contribution-id, validator: tx-sender })))
              ERR-ALREADY-VALIDATED)
    (map-set contribution-validators
      { contribution-id: contribution-id, validator: tx-sender }
      true)
    (let ((new-count (+ (get validation-count contrib) u1)))
      (if (>= new-count u3)
        (begin
          (map-set contributions contribution-id
            (merge contrib { validation-count: new-count, validated: true }))
          ;; Award expertise points to contributor
          (let ((dom (get domain contrib))
                (contributor (get contributor contrib)))
            (map-set expertise-scores
              { user: contributor, domain: dom }
              (+ (get-expertise contributor dom) u25))
            (ok true)))
        (begin
          (map-set contributions contribution-id
            (merge contrib { validation-count: new-count }))
          (ok false))))))

;; ===========================
;; PROPOSAL LIFECYCLE
;; ===========================

;; Submit a new proposal. Proposer must hold MIN-PROPOSAL-TOKENS.
(define-public (submit-proposal
    (title (string-ascii 128))
    (description (string-ascii 1024)))
  (begin
    (asserts! (>= (get-balance tx-sender) MIN-PROPOSAL-TOKENS)
              ERR-INSUFFICIENT-TOKENS)
    (let ((pid (+ (var-get proposal-nonce) u1)))
      (var-set proposal-nonce pid)
      (map-set proposals pid {
        proposer:           tx-sender,
        title:              title,
        description:        description,
        created-at-block:   block-height,
        voting-ends-block:  (+ block-height VOTING-PERIOD-BLOCKS),
        execution-block:    (+ block-height VOTING-PERIOD-BLOCKS LOCK-PERIOD-BLOCKS),
        stage:              STAGE-SUBMITTED,
        yes-votes:          u0,
        no-votes:           u0,
        total-voting-power: u0,
        technical-score:    u0,
        economic-score:     u0,
        executed:           false,
        approved:           false
      })
      (ok pid))))

;; Technical feasibility scoring (stage 1 -> stage 2)
;; Score range: 0-100
(define-public (score-technical (proposal-id uint) (score uint))
  (begin
    (asserts! (default-to false (map-get? technical-scorers tx-sender))
              ERR-NOT-AUTHORIZED)
    (asserts! (<= score u100) ERR-INVALID-VOTES)
    (let ((proposal (unwrap! (map-get? proposals proposal-id) ERR-PROPOSAL-NOT-FOUND)))
      (asserts! (is-eq (get stage proposal) STAGE-SUBMITTED) ERR-PROPOSAL-NOT-ACTIVE)
      (map-set proposals proposal-id
        (merge proposal {
          technical-score: score,
          stage:           STAGE-TECHNICAL
        }))
      (ok true))))

;; Economic impact scoring (stage 2 -> stage 3 / voting open)
;; Score range: 0-100
(define-public (score-economic (proposal-id uint) (score uint))
  (begin
    (asserts! (default-to false (map-get? economic-scorers tx-sender))
              ERR-NOT-AUTHORIZED)
    (asserts! (<= score u100) ERR-INVALID-VOTES)
    (let ((proposal (unwrap! (map-get? proposals proposal-id) ERR-PROPOSAL-NOT-FOUND)))
      (asserts! (is-eq (get stage proposal) STAGE-TECHNICAL) ERR-PROPOSAL-NOT-ACTIVE)
      (map-set proposals proposal-id
        (merge proposal {
          economic-score: score,
          stage:          STAGE-VOTING
        }))
      (ok true))))

;; Cast a quadratic vote on an active proposal.
;; votes: number of vote units (cost = votes^2 governance tokens)
;; support: true = yes, false = no
(define-public (cast-vote
    (proposal-id uint)
    (votes uint)
    (support bool))
  (begin
    (asserts! (> votes u0) ERR-INVALID-VOTES)
    (asserts! (<= votes MAX-VOTES-PER-USER) ERR-INVALID-VOTES)
    (let ((proposal (unwrap! (map-get? proposals proposal-id) ERR-PROPOSAL-NOT-FOUND)))
      (asserts! (is-eq (get stage proposal) STAGE-VOTING) ERR-PROPOSAL-NOT-ACTIVE)
      (asserts! (<= block-height (get voting-ends-block proposal)) ERR-PROPOSAL-EXPIRED)
      (asserts! (not (default-to false
                       (map-get? has-voted { proposal-id: proposal-id, voter: tx-sender })))
                ERR-ALREADY-VOTED)
      (let ((cost (quadratic-cost votes)))
        (asserts! (>= (get-balance tx-sender) cost) ERR-INSUFFICIENT-TOKENS)
        ;; Lock tokens (subtract from balance, simulating a lock for the voting period)
        (map-set token-balances tx-sender (- (get-balance tx-sender) cost))
        ;; Record vote
        (map-set has-voted { proposal-id: proposal-id, voter: tx-sender } true)
        ;; Compute weighted power
        (let ((power (weighted-voting-power tx-sender votes)))
          (if support
            (map-set proposals proposal-id
              (merge proposal {
                yes-votes:          (+ (get yes-votes proposal) power),
                total-voting-power: (+ (get total-voting-power proposal) power)
              }))
            (map-set proposals proposal-id
              (merge proposal {
                no-votes:           (+ (get no-votes proposal) power),
                total-voting-power: (+ (get total-voting-power proposal) power)
              })))
          ;; Award active participation bonus
          (map-set token-balances tx-sender
            (+ (get-balance tx-sender) ACTIVE-PARTICIPANT-BONUS))
          ;; Grant community expertise for voting participation
          (map-set expertise-scores
            { user: tx-sender, domain: DOMAIN-COMMUNITY }
            (+ (get-expertise tx-sender DOMAIN-COMMUNITY) u5))
          (ok power))))))

;; Finalize a proposal after the voting period ends.
;; Checks quorum and approval threshold.
;; Burns tokens from proposer on failure; marks approved on success.
(define-public (finalize-proposal (proposal-id uint))
  (let ((proposal (unwrap! (map-get? proposals proposal-id) ERR-PROPOSAL-NOT-FOUND)))
    (asserts! (is-eq (get stage proposal) STAGE-VOTING) ERR-PROPOSAL-NOT-ACTIVE)
    (asserts! (> block-height (get voting-ends-block proposal)) ERR-PROPOSAL-NOT-ENDED)
    (let ((total-power (get total-voting-power proposal))
          (yes-power   (get yes-votes proposal))
          (supply      (var-get total-supply)))
      ;; Quorum: total voting power >= QUORUM-THRESHOLD% of supply
      (let ((quorum-met (>= (* total-power u100) (* supply QUORUM-THRESHOLD))))
        (let ((approval-met
               (if (> total-power u0)
                 (>= (* yes-power u100) (* total-power APPROVAL-THRESHOLD))
                 false)))
          (if (and quorum-met approval-met)
            (begin
              (map-set proposals proposal-id
                (merge proposal { stage: STAGE-ENDED, approved: true }))
              (ok true))
            (begin
              ;; Burn tokens from proposer for failed proposal
              (burn-tokens-from (get proposer proposal) BURN-ON-FAILURE)
              (map-set proposals proposal-id
                (merge proposal { stage: STAGE-ENDED, approved: false }))
              (ok false))))))))

;; Execute an approved proposal after the timelock period.
;; Marks it as executed; external integration hooks can be added here.
(define-public (execute-proposal (proposal-id uint))
  (let ((proposal (unwrap! (map-get? proposals proposal-id) ERR-PROPOSAL-NOT-FOUND)))
    (asserts! (is-eq (get stage proposal) STAGE-ENDED) ERR-PROPOSAL-NOT-ENDED)
    (asserts! (get approved proposal) ERR-NOT-APPROVED)
    (asserts! (not (get executed proposal)) ERR-ALREADY-EXECUTED)
    (asserts! (>= block-height (get execution-block proposal)) ERR-PROPOSAL-NOT-ENDED)
    (map-set proposals proposal-id
      (merge proposal { stage: STAGE-EXECUTED, executed: true }))
    ;; Expertise reward for successful proposer
    (map-set expertise-scores
      { user: (get proposer proposal), domain: DOMAIN-COMMUNITY }
      (+ (get-expertise (get proposer proposal) DOMAIN-COMMUNITY) u50))
    (ok true)))

;; ===========================
;; READ-ONLY FUNCTIONS
;; ===========================

;; Get governance token balance
(define-read-only (get-token-balance (user principal))
  (get-balance user))

;; Get total token supply
(define-read-only (get-total-supply)
  (var-get total-supply))

;; Get proposal details
(define-read-only (get-proposal (proposal-id uint))
  (map-get? proposals proposal-id))

;; Check if a user has voted on a proposal
(define-read-only (has-user-voted (proposal-id uint) (user principal))
  (default-to false (map-get? has-voted { proposal-id: proposal-id, voter: user })))

;; Get expertise score for a user in a domain
(define-read-only (get-expertise-score (user principal) (domain uint))
  (get-expertise user domain))

;; Get expertise multiplier for a user in a domain
(define-read-only (get-expertise-multiplier (user principal) (domain uint))
  (expertise-multiplier user domain))

;; Compute quadratic cost for a given number of votes
(define-read-only (compute-vote-cost (votes uint))
  (quadratic-cost votes))

;; Get contribution details
(define-read-only (get-contribution (contribution-id uint))
  (map-get? contributions contribution-id))

;; Get current proposal count
(define-read-only (get-proposal-count)
  (var-get proposal-nonce))

;; Get current contribution count
(define-read-only (get-contribution-count)
  (var-get contribution-nonce))

;; Check if a principal is a technical scorer
(define-read-only (is-technical-scorer (user principal))
  (default-to false (map-get? technical-scorers user)))

;; Check if a principal is an economic scorer
(define-read-only (is-economic-scorer (user principal))
  (default-to false (map-get? economic-scorers user)))

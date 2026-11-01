-- Prove2me | solution 1 for OpenSearchPreVote.votes_mem
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:51:23.259343+00:00
-- url     : https://prove2.me/submissions/f8105298-7186-4b77-98d6-b31e16934fb8

import Definitions.Def_OpenSearchPreVote

open OpenSearchCoordination OpenSearchPreVote

/-- Counting: an element satisfying both `p` and `q` is counted at most twice on the left and once on each side. -/
private theorem pv_filter_length_add_le {α : Type} (L : List α) (p q : α → Bool) :
    (L.filter p).length + (L.filter q).length ≤ L.length + (L.filter (fun x => p x && q x)).length := by
  induction L with
  | nil => simp
  | cons y ys ih =>
    cases hp : p y <;> cases hq : q y <;> simp [hp, hq] <;> omega

/-- Two quorums of the same voting configuration share a member of the configuration. -/
private theorem pv_quorum_intersect (c : VotingConfiguration) (a b : List NodeId)
    (ha : c.hasQuorum a = true) (hb : c.hasQuorum b = true) :
    ∃ x, x ∈ c.nodeIds ∧ x ∈ a ∧ x ∈ b := by
  simp only [VotingConfiguration.hasQuorum, decide_eq_true_eq] at ha hb
  have key := pv_filter_length_add_le c.nodeIds (fun x => a.contains x) (fun x => b.contains x)
  have hpos : 0 < (c.nodeIds.filter (fun x => a.contains x && b.contains x)).length := by omega
  obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos hpos
  rw [List.mem_filter, Bool.and_eq_true, List.contains_iff_mem, List.contains_iff_mem] at hx
  exact ⟨x, hx.1, hx.2.1, hx.2.2⟩

/-- Filtering by a weaker predicate keeps at least as many elements. -/
private theorem pv_filter_length_mono {α : Type} (L : List α) (p q : α → Bool)
    (h : ∀ x, p x = true → q x = true) :
    (L.filter p).length ≤ (L.filter q).length := by
  induction L with
  | nil => simp
  | cons y ys ih =>
    cases hp : p y <;> cases hq : q y <;> simp [hp, hq] <;> try omega
    have := h y hp
    rw [hq] at this
    exact absurd this (by decide)

/-- A superset of a quorum is a quorum. -/
private theorem pv_quorum_mono (c : VotingConfiguration) (a b : List NodeId) (hab : ∀ x, x ∈ a → x ∈ b)
    (ha : c.hasQuorum a = true) : c.hasQuorum b = true := by
  simp only [VotingConfiguration.hasQuorum, decide_eq_true_eq] at ha ⊢
  have := pv_filter_length_mono c.nodeIds (fun x => a.contains x) (fun x => b.contains x)
    (fun x hx => by rw [List.contains_iff_mem] at hx ⊢; exact hab x hx)
  omega

/-- A configuration that has a quorum is nonempty. -/
private theorem pv_quorum_nonempty (c : VotingConfiguration) (a : List NodeId) (ha : c.hasQuorum a = true) :
    c.isEmpty = false := by
  unfold VotingConfiguration.hasQuorum at ha
  unfold VotingConfiguration.isEmpty
  cases h : c.nodeIds with
  | nil => rw [h] at ha; simp at ha
  | cons y ys => rfl

/-- An empty vote collection is a quorum of no configuration. -/
private theorem pv_no_votes_no_quorum (c : VotingConfiguration) : VoteCollection.empty.isQuorum c = false := by
  unfold VoteCollection.isQuorum VotingConfiguration.hasQuorum VoteCollection.empty
  dsimp only
  rw [decide_eq_false_iff_not]
  have : (c.nodeIds.filter (fun x => ([] : List NodeId).contains x)).length = 0 := by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]; simp
  omega

/-- `addVote` adds exactly the id of a cluster-manager-eligible node. -/
private theorem pv_addVote_eligible (v : VoteCollection) (n : DiscoveryNode) (x : NodeId) :
    x ∈ (v.addVote n).1.nodes ↔ x ∈ v.nodes ∨ (x = n.id ∧ n.isClusterManagerNode = true) := by
  unfold VoteCollection.addVote
  split
  · rename_i h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
    simp only [List.mem_cons, h.1, and_true]
    exact Or.comm
  · rename_i h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
      not_and, Classical.not_not] at h
    constructor
    · exact Or.inl
    · rintro (hx | ⟨rfl, hc⟩)
      · exact hx
      · exact h hc

/-- `handleStartJoin` succeeds exactly when the requested term is greater than the current term. -/
private theorem pv_handleStartJoin_spec {V : Type} (cs : CoordinationState V) (req : StartJoinRequest)
    (cs' : CoordinationState V) (j : Join) :
    cs.handleStartJoin req = .ok (cs', j) ↔
      cs.currentTerm < req.term ∧ cs'.currentTerm = req.term ∧ cs'.lastAcceptedState = cs.lastAcceptedState ∧
      cs'.localNode = cs.localNode ∧ cs'.startedJoinSinceLastReboot = true ∧ cs'.electionWon = false ∧
      cs'.joinVotes = VoteCollection.empty ∧ cs'.publishVotes = VoteCollection.empty ∧
      cs'.lastPublishedVersion = 0 ∧ cs'.lastPublishedConfiguration = cs.lastAcceptedConfiguration ∧
      j = ⟨cs.localNode, req.sourceNode, req.term, cs.lastAcceptedTerm, cs.lastAcceptedVersionOrMetadataVersion⟩ := by
  unfold CoordinationState.handleStartJoin
  constructor
  · intro h
    split at h
    · cases h
    · rename_i hlt
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by omega, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨hlt, h1, h2, h3, h4, h5, h6, h7, h8, h9, rfl⟩
    rw [if_neg (show ¬ (req.term ≤ cs.currentTerm) by omega)]
    obtain ⟨ln, ct, las, jv, sj, ew, lpv, lpc, pv⟩ := cs'
    dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9
    subst h1 h2 h3 h4 h5 h6 h7 h8 h9
    rfl

/-- A successful `handleJoin` adds the source's vote, recomputes `electionWon`, and changes neither the current term,
the accepted state, the local node nor `startedJoinSinceLastReboot`. -/
private theorem pv_handleJoin_ok_spec {V : Type} (es : ElectionStrategy) (cs : CoordinationState V) (j : Join)
    (cs' : CoordinationState V) (b : Bool) (h : cs.handleJoin es j = .ok (cs', b)) :
    cs'.joinVotes = (cs.joinVotes.addVote j.sourceNode).1 ∧
    cs'.electionWon = cs.isElectionQuorum es cs'.joinVotes ∧
    cs'.currentTerm = cs.currentTerm ∧ cs'.lastAcceptedState = cs.lastAcceptedState ∧
    cs'.localNode = cs.localNode ∧ cs'.startedJoinSinceLastReboot = cs.startedJoinSinceLastReboot := by
  unfold CoordinationState.handleJoin at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  generalize hva : cs.joinVotes.addVote j.sourceNode = va at h
  obtain ⟨votes, added⟩ := va
  dsimp only at h
  split at h
  all_goals
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `handleJoin` succeeds on a join for the current term, after a start-join since the last reboot, from a voter whose
accepted state is no fresher, once the node has an accepted configuration. -/
private theorem pv_handleJoin_succeeds {V : Type} (es : ElectionStrategy) (cs : CoordinationState V) (j : Join)
    (h1 : j.term = cs.currentTerm) (h2 : cs.startedJoinSinceLastReboot = true)
    (h3 : j.lastAcceptedTerm < cs.lastAcceptedTerm ∨
      (j.lastAcceptedTerm = cs.lastAcceptedTerm ∧ j.lastAcceptedVersion ≤ cs.lastAcceptedVersionOrMetadataVersion))
    (h4 : cs.lastAcceptedConfiguration.isEmpty = false) :
    ∃ cs' b, cs.handleJoin es j = .ok (cs', b) := by
  unfold CoordinationState.handleJoin
  split
  · rename_i h; exact absurd h1 h
  split
  · rename_i h; simp [h2] at h
  split
  · rename_i h; omega
  split
  · rename_i h; omega
  split
  · rename_i h; simp [h4] at h
  exact ⟨_, _, rfl⟩

/-- `isElectionQuorum` reads only the local node, the current term and the accepted state. -/
private theorem pv_isElectionQuorum_congr {V : Type} (es : ElectionStrategy) (cs cs' : CoordinationState V)
    (h1 : cs'.localNode = cs.localNode) (h2 : cs'.currentTerm = cs.currentTerm)
    (h3 : cs'.lastAcceptedState = cs.lastAcceptedState) (v : VoteCollection) :
    cs'.isElectionQuorum es v = cs.isElectionQuorum es v := by
  unfold CoordinationState.isElectionQuorum CoordinationState.lastCommittedConfiguration
    CoordinationState.lastAcceptedConfiguration CoordinationState.lastAcceptedTerm
    CoordinationState.lastAcceptedVersion
  rw [h1, h2, h3]

/-- Handling a sequence of joins changes neither the current term, the accepted state, the local node nor
`startedJoinSinceLastReboot`; the votes only grow; `electionWon` stays the election-quorum status of the votes; and the
vote of every join in the sequence that passes `handleJoin`'s checks (which read only the unchanged fields) is
counted when its source is cluster-manager-eligible. -/
private theorem pv_handleJoins_spec {V : Type} (es : ElectionStrategy) (js : List Join) :
    ∀ cs : CoordinationState V,
    (handleJoins es cs js).currentTerm = cs.currentTerm ∧
    (handleJoins es cs js).lastAcceptedState = cs.lastAcceptedState ∧
    (handleJoins es cs js).localNode = cs.localNode ∧
    (handleJoins es cs js).startedJoinSinceLastReboot = cs.startedJoinSinceLastReboot ∧
    (∀ x, x ∈ cs.joinVotes.nodes → x ∈ (handleJoins es cs js).joinVotes.nodes) ∧
    (cs.electionWon = cs.isElectionQuorum es cs.joinVotes →
      (handleJoins es cs js).electionWon =
        (handleJoins es cs js).isElectionQuorum es (handleJoins es cs js).joinVotes) ∧
    (∀ j ∈ js, j.term = cs.currentTerm → cs.startedJoinSinceLastReboot = true →
      (j.lastAcceptedTerm < cs.lastAcceptedTerm ∨
        (j.lastAcceptedTerm = cs.lastAcceptedTerm ∧ j.lastAcceptedVersion ≤ cs.lastAcceptedVersionOrMetadataVersion)) →
      cs.lastAcceptedConfiguration.isEmpty = false → j.sourceNode.isClusterManagerNode = true →
      j.sourceNode.id ∈ (handleJoins es cs js).joinVotes.nodes) := by
  induction js with
  | nil =>
    intro cs
    refine ⟨rfl, rfl, rfl, rfl, fun x hx => hx, fun h => h, ?_⟩
    intro j hj
    cases hj
  | cons j js ih =>
    intro cs
    obtain ⟨cs₁, hstep, hcases⟩ : ∃ cs₁, handleJoins es cs (j :: js) = handleJoins es cs₁ js ∧
        ((cs₁ = cs ∧ ∀ cs' b, cs.handleJoin es j ≠ .ok (cs', b)) ∨ ∃ b, cs.handleJoin es j = .ok (cs₁, b)) := by
      cases h : cs.handleJoin es j with
      | ok p =>
        obtain ⟨cs', b⟩ := p
        exact ⟨cs', by simp only [handleJoins, List.foldl_cons, h], Or.inr ⟨b, rfl⟩⟩
      | error e =>
        exact ⟨cs, by simp only [handleJoins, List.foldl_cons, h], Or.inl ⟨rfl, fun _ _ h' => by cases h'⟩⟩
    -- the step `cs → cs₁`
    have hfields : cs₁.currentTerm = cs.currentTerm ∧ cs₁.lastAcceptedState = cs.lastAcceptedState ∧
        cs₁.localNode = cs.localNode ∧ cs₁.startedJoinSinceLastReboot = cs.startedJoinSinceLastReboot ∧
        (∀ x, x ∈ cs.joinVotes.nodes → x ∈ cs₁.joinVotes.nodes) ∧
        (cs.electionWon = cs.isElectionQuorum es cs.joinVotes → cs₁.electionWon = cs₁.isElectionQuorum es cs₁.joinVotes) := by
      rcases hcases with ⟨rfl, -⟩ | ⟨b, hb⟩
      · exact ⟨rfl, rfl, rfl, rfl, fun x hx => hx, fun h => h⟩
      · obtain ⟨hv, hw, hct, hlas, hln, hsj⟩ := pv_handleJoin_ok_spec es cs j cs₁ b hb
        refine ⟨hct, hlas, hln, hsj, ?_, ?_⟩
        · intro x hx
          rw [hv, pv_addVote_eligible]
          exact Or.inl hx
        · intro _
          rw [hw, pv_isElectionQuorum_congr es cs cs₁ hln hct hlas]
    obtain ⟨hct, hlas, hln, hsj, hsub, hinv⟩ := hfields
    obtain ⟨ih1, ih2, ih3, ih4, ih5, ih6, ih7⟩ := ih cs₁
    rw [hstep]
    refine ⟨ih1.trans hct, ih2.trans hlas, ih3.trans hln, ih4.trans hsj, fun x hx => ih5 x (hsub x hx),
      fun h => ih6 (hinv h), ?_⟩
    have hlat : cs₁.lastAcceptedTerm = cs.lastAcceptedTerm := by
      unfold CoordinationState.lastAcceptedTerm; rw [hlas]
    have hlav : cs₁.lastAcceptedVersionOrMetadataVersion = cs.lastAcceptedVersionOrMetadataVersion := by
      unfold CoordinationState.lastAcceptedVersionOrMetadataVersion; rw [hlas]
    have hlac : cs₁.lastAcceptedConfiguration = cs.lastAcceptedConfiguration := by
      unfold CoordinationState.lastAcceptedConfiguration; rw [hlas]
    intro j' hj' g1 g2 g3 g4 g5
    rcases List.mem_cons.1 hj' with rfl | hj'
    · -- the head join passes the checks, so it succeeds and its vote is counted
      obtain ⟨cs', b, hok⟩ := pv_handleJoin_succeeds es cs j' g1 g2 g3 g4
      rcases hcases with ⟨-, hne⟩ | ⟨b', hb'⟩
      · exact absurd hok (hne cs' b)
      · apply ih5
        obtain ⟨hv, -⟩ := pv_handleJoin_ok_spec es cs j' cs₁ b' hb'
        rw [hv, pv_addVote_eligible]
        exact Or.inr ⟨rfl, g5⟩
    · exact ih7 j' hj' (g1.trans hct.symm) (hsj.trans g2) (by rw [hlat, hlav]; exact g3) (by rw [hlac]; exact g4) g5

/-- The ids counted by the fold of `PreVotingRound.votes`. -/
private theorem pv_foldr_votes_mem (l : List (DiscoveryNode × PreVoteResponse)) (x : NodeId) :
    x ∈ (l.foldr (fun p v => (v.addVote p.1).1) VoteCollection.empty).nodes ↔
      ∃ p ∈ l, p.1.id = x ∧ p.1.isClusterManagerNode = true := by
  induction l with
  | nil => simp [VoteCollection.empty]
  | cons q qs ih =>
    rw [List.foldr_cons, pv_addVote_eligible, ih]
    constructor
    · rintro (⟨p, hp, h1, h2⟩ | ⟨rfl, h2⟩)
      · exact ⟨p, List.mem_cons_of_mem _ hp, h1, h2⟩
      · exact ⟨q, by simp, rfl, h2⟩
    · rintro ⟨p, hp, h1, h2⟩
      rcases List.mem_cons.1 hp with rfl | hp
      · exact Or.inr ⟨h1.symm, h2⟩
      · exact Or.inl ⟨p, hp, h1, h2⟩

/-- What a response does to a round: the accepted state and the local node are unchanged; either the recorded responses
are unchanged, or the response is no fresher than the round's accepted state and replaces any earlier response of the
same sender; the round starts an election (or has started one) only when the recorded responses form an election
quorum. -/
private theorem pv_handle_shape {V : Type} (es : ElectionStrategy) (lr resp : PreVoteResponse) (r : PreVotingRound V)
    (sender : DiscoveryNode) :
    (r.handlePreVoteResponse es lr resp sender).1.clusterState = r.clusterState ∧
    (r.handlePreVoteResponse es lr resp sender).1.localNode = r.localNode ∧
    ((r.handlePreVoteResponse es lr resp sender).1.preVotesReceived = r.preVotesReceived ∨
      (NoFresher resp r.clusterState ∧
        (r.handlePreVoteResponse es lr resp sender).1.preVotesReceived =
          (sender, resp) :: r.preVotesReceived.filter (fun p => p.1 ≠ sender))) ∧
    ((r.handlePreVoteResponse es lr resp sender).1.electionStarted = true →
      r.electionStarted = true ∨
      isElectionQuorumFor es r.localNode lr.currentTerm lr.lastAcceptedTerm lr.lastAcceptedVersion
        r.clusterState.lastCommittedConfiguration r.clusterState.lastAcceptedConfiguration
        (r.handlePreVoteResponse es lr resp sender).1.votes = true) ∧
    ((r.handlePreVoteResponse es lr resp sender).2.1 = true →
      isElectionQuorumFor es r.localNode lr.currentTerm lr.lastAcceptedTerm lr.lastAcceptedVersion
        r.clusterState.lastCommittedConfiguration r.clusterState.lastAcceptedConfiguration
        (r.handlePreVoteResponse es lr resp sender).1.votes = true) := by
  unfold PreVotingRound.handlePreVoteResponse
  split
  · exact ⟨rfl, rfl, Or.inl rfl, fun h => Or.inl h, fun h => absurd h Bool.false_ne_true⟩
  · split
    · exact ⟨rfl, rfl, Or.inl rfl, fun h => Or.inl h, fun h => absurd h Bool.false_ne_true⟩
    · rename_i hf
      have hnf : NoFresher resp r.clusterState := by
        unfold NoFresher; omega
      dsimp only
      split
      · exact ⟨rfl, rfl, Or.inr ⟨hnf, rfl⟩, fun h => Or.inl h, fun h => absurd h Bool.false_ne_true⟩
      · rename_i hq
        have hq' : isElectionQuorumFor es r.localNode lr.currentTerm lr.lastAcceptedTerm lr.lastAcceptedVersion
            r.clusterState.lastCommittedConfiguration r.clusterState.lastAcceptedConfiguration
            ({ r with preVotesReceived := (sender, resp) :: r.preVotesReceived.filter (fun p => p.1 ≠ sender) } :
              PreVotingRound V).votes = true := by
          simpa using hq
        split
        · exact ⟨rfl, rfl, Or.inr ⟨hnf, rfl⟩, fun _ => Or.inr hq', fun _ => hq'⟩
        · exact ⟨rfl, rfl, Or.inr ⟨hnf, rfl⟩, fun _ => Or.inr hq', fun _ => hq'⟩

/-- The votes a round counts are exactly the ids of the cluster-manager-eligible senders it has recorded. -/
theorem solution {V : Type} (r : PreVotingRound V) (x : NodeId) :
    x ∈ r.votes.nodes ↔ ∃ p ∈ r.preVotesReceived, p.1.id = x ∧ p.1.isClusterManagerNode = true := by
  unfold PreVotingRound.votes
  exact pv_foldr_votes_mem r.preVotesReceived x

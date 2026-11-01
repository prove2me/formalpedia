-- Prove2me | solution 1 for OpenSearchPreVote.preVote_then_election
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:51:49.38363+00:00
-- url     : https://prove2.me/submissions/d06f9829-65fa-4e1e-bb74-b75aaf00d16e

import Definitions.Def_OpenSearchPreVote
import Theorems.Thm_OpenSearchPreVote_round_entries
import Theorems.Thm_OpenSearchPreVote_votes_mem

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

/-- The election-quorum check of a round fails when the counted votes avoid a quorum of one of the configurations. -/
private theorem pv_not_election_quorum (es : ElectionStrategy) (ln : DiscoveryNode) (ct at' : Nat) (av : Int)
    (committed accepted : VotingConfiguration) (votes : VoteCollection) (L : List NodeId)
    (hL : committed.hasQuorum L = true ∨ accepted.hasQuorum L = true)
    (hdisj : ∀ x, x ∈ votes.nodes → x ∉ L) :
    isElectionQuorumFor es ln ct at' av committed accepted votes = false := by
  unfold isElectionQuorumFor VoteCollection.isQuorum
  rcases hL with hL | hL
  · cases hq : committed.hasQuorum votes.nodes
    · rfl
    · obtain ⟨x, -, hx1, hx2⟩ := pv_quorum_intersect committed L votes.nodes hL hq
      exact absurd hx1 (hdisj x hx2)
  · cases hq : accepted.hasQuorum votes.nodes
    · simp
    · obtain ⟨x, -, hx1, hx2⟩ := pv_quorum_intersect accepted L votes.nodes hL hq
      exact absurd hx1 (hdisj x hx2)

/-- The senders a round records only accumulate: re-sent responses replace earlier ones of the same sender. -/
private theorem pv_votes_grow {V : Type} (r r' : PreVotingRound V) (sender : DiscoveryNode) (resp : PreVoteResponse)
    (h : r'.preVotesReceived = r.preVotesReceived ∨
      r'.preVotesReceived = (sender, resp) :: r.preVotesReceived.filter (fun p => p.1 ≠ sender)) :
    ∀ x, x ∈ r.votes.nodes → x ∈ r'.votes.nodes := by
  intro x hx
  rw [OpenSearchPreVote.votes_mem] at hx ⊢
  obtain ⟨p, hp, h1, h2⟩ := hx
  rcases h with h | h
  · exact ⟨p, h ▸ hp, h1, h2⟩
  · rw [h]
    by_cases hps : p.1 = sender
    · exact ⟨(sender, resp), by simp, hps ▸ h1, hps ▸ h2⟩
    · exact ⟨p, List.mem_cons_of_mem _ (List.mem_filter.2 ⟨hp, by simpa using hps⟩), h1, h2⟩

/-- A round that has started an election has recorded votes forming a quorum of both configurations of the state it
started from (whatever the election strategy). -/
private theorem pv_started_quorum {V : Type} (es : ElectionStrategy) (D : DiscoveryNode → PreVoteResponse → Prop)
    (r : PreVotingRound V) (hr : RoundReachable es D r) (h : r.electionStarted = true) :
    r.votes.isQuorum r.clusterState.lastCommittedConfiguration = true ∧
    r.votes.isQuorum r.clusterState.lastAcceptedConfiguration = true := by
  induction hr with
  | start s n => cases h
  | handle r lr resp sender _ hd ih =>
    obtain ⟨hcs, -, hpv, hst, -⟩ := pv_handle_shape es lr resp r sender
    rw [hcs]
    rcases hst h with h' | hq
    · obtain ⟨ih1, ih2⟩ := ih h'
      have hsub := pv_votes_grow r (r.handlePreVoteResponse es lr resp sender).1 sender resp
        (by rcases hpv with hpv | ⟨-, hpv⟩
            · exact Or.inl hpv
            · exact Or.inr hpv)
      exact ⟨pv_quorum_mono _ _ _ hsub ih1, pv_quorum_mono _ _ _ hsub ih2⟩
    · unfold isElectionQuorumFor at hq
      simp only [Bool.and_eq_true] at hq
      exact ⟨hq.1.1, hq.1.2⟩
  | close r _ ih => exact ih h

/-- **A successful pre-vote predicts a successful election.** Let node `c` (with the default election strategy) run a
pre-voting round over its accepted state, with itself as the round's local node, every recorded response from a node
`n` being `preVoteResponseOf (node n)`, where `node n`, whose local node is `n`, is the coordination state in which `n`
handles `c`'s `StartJoinRequest` (the senders have not changed state since answering), and let the round have started
an election. Let `T` be the election's term: one above the larger of `c`'s current term and a `maxTermSeen` that is at
least the current term of every recorded response. Let `c` handle its own `StartJoinRequest` for `T`. Then every
recorded sender accepts that request, and if the joins they produce are among the joins `c` then handles, in any
order — interleaved with any other joins of a term at most `T`, accepted or not, and nothing else — the resulting
state of `c` has `electionWon = true`. -/
theorem solution {V : Type} (csc : CoordinationState V)
    (node : DiscoveryNode → CoordinationState V) (r : PreVotingRound V)
    (hr : RoundReachable ElectionStrategy.DEFAULT_INSTANCE
      (fun n resp => (node n).localNode = n ∧ preVoteResponseOf (node n) = resp) r)
    (hstate : r.clusterState = csc.lastAcceptedState) (hlocal : r.localNode = csc.localNode)
    (hstarted : r.electionStarted = true) (maxTermSeen : Nat)
    (hseen : ∀ p ∈ r.preVotesReceived, p.2.currentTerm ≤ maxTermSeen)
    (csc₁ : CoordinationState V) (j₀ : Join)
    (hsj : csc.handleStartJoin ⟨csc.localNode, startElectionTerm csc.currentTerm maxTermSeen⟩ = .ok (csc₁, j₀))
    (js : List Join) (hjs : ∀ j ∈ js, j.term ≤ startElectionTerm csc.currentTerm maxTermSeen) :
    (∀ p ∈ r.preVotesReceived, ∃ cs' j,
      (node p.1).handleStartJoin ⟨csc.localNode, startElectionTerm csc.currentTerm maxTermSeen⟩ = .ok (cs', j)) ∧
    ((∀ p ∈ r.preVotesReceived, ∀ cs' j,
      (node p.1).handleStartJoin ⟨csc.localNode, startElectionTerm csc.currentTerm maxTermSeen⟩ = .ok (cs', j) →
        j ∈ js) →
      (handleJoins ElectionStrategy.DEFAULT_INSTANCE csc₁ js).electionWon = true) := by
  -- (the default strategy has no additional quorum constraint, so the round's local node plays no role)
  have _ := hlocal
  -- (joins of a higher term would first move `c` to that term in the Coordinator; the hypothesis `hjs` excludes them,
  -- and the transcribed `handleJoin` rejects them)
  have _ := hjs
  -- the state of `c` after its own start-join
  obtain ⟨-, hct₁, hlas₁, -, hsj₁, hew₁, hjv₁, -⟩ := (pv_handleStartJoin_spec _ _ _ _).1 hsj
  -- the recorded entries, and the quorum they form
  have hent := (round_entries _ _ r hr).1
  obtain ⟨hqc, hqa⟩ := pv_started_quorum _ _ r hr hstarted
  -- every recorded sender accepts the start-join request
  have hpart1 : ∀ p ∈ r.preVotesReceived, ∃ cs' j,
      (node p.1).handleStartJoin ⟨csc.localNode, startElectionTerm csc.currentTerm maxTermSeen⟩ = .ok (cs', j) := by
    intro p hp
    obtain ⟨-, -, hresp⟩ := hent p hp
    have hct : (node p.1).currentTerm = p.2.currentTerm := by rw [← hresp]; rfl
    have hle := hseen p hp
    unfold CoordinationState.handleStartJoin
    rw [if_neg (show ¬ (startElectionTerm csc.currentTerm maxTermSeen ≤ (node p.1).currentTerm) by
      unfold startElectionTerm; omega)]
    exact ⟨_, _, rfl⟩
  refine ⟨hpart1, ?_⟩
  intro hjs
  obtain ⟨-, hlas', -, -, -, hinv, hgood⟩ := pv_handleJoins_spec ElectionStrategy.DEFAULT_INSTANCE js csc₁
  have hinv₁ : csc₁.electionWon = csc₁.isElectionQuorum ElectionStrategy.DEFAULT_INSTANCE csc₁.joinVotes := by
    rw [hew₁, hjv₁]
    unfold CoordinationState.isElectionQuorum
    rw [pv_no_votes_no_quorum]
    rfl
  rw [hinv hinv₁]
  -- the configurations of the final state are those of the round
  have hcomm : (handleJoins ElectionStrategy.DEFAULT_INSTANCE csc₁ js).lastCommittedConfiguration =
      r.clusterState.lastCommittedConfiguration := by
    unfold CoordinationState.lastCommittedConfiguration; rw [hlas', hlas₁, hstate]
  have hacc : (handleJoins ElectionStrategy.DEFAULT_INSTANCE csc₁ js).lastAcceptedConfiguration =
      r.clusterState.lastAcceptedConfiguration := by
    unfold CoordinationState.lastAcceptedConfiguration; rw [hlas', hlas₁, hstate]
  have hacc₁ : csc₁.lastAcceptedConfiguration = r.clusterState.lastAcceptedConfiguration := by
    unfold CoordinationState.lastAcceptedConfiguration; rw [hlas₁, hstate]
  -- the votes of the round are counted in the end
  have hsub : ∀ x, x ∈ r.votes.nodes → x ∈ (handleJoins ElectionStrategy.DEFAULT_INSTANCE csc₁ js).joinVotes.nodes := by
    intro x hx
    obtain ⟨p, hp, hpx, hpe⟩ := (votes_mem r x).1 hx
    obtain ⟨hnf, hloc, hresp⟩ := hent p hp
    obtain ⟨cs', j, hsjp⟩ := hpart1 p hp
    have hjmem := hjs p hp cs' j hsjp
    obtain ⟨-, -, -, -, -, -, -, -, -, -, rfl⟩ := (pv_handleStartJoin_spec _ _ _ _).1 hsjp
    have hlat : (node p.1).lastAcceptedTerm = p.2.lastAcceptedTerm := by rw [← hresp]; rfl
    have hlav : (node p.1).lastAcceptedVersionOrMetadataVersion = p.2.lastAcceptedVersion := by rw [← hresp]; rfl
    have hlat₁ : csc₁.lastAcceptedTerm = r.clusterState.term := by
      unfold CoordinationState.lastAcceptedTerm; rw [hlas₁, hstate]
    have hlav₁ : csc₁.lastAcceptedVersionOrMetadataVersion = r.clusterState.versionOrMetadataVersion := by
      unfold CoordinationState.lastAcceptedVersionOrMetadataVersion; rw [hlas₁, hstate]
    have := hgood _ hjmem hct₁.symm hsj₁ (by
        dsimp only
        rw [hlat, hlav, hlat₁, hlav₁]
        exact hnf)
      (by rw [hacc₁]; exact pv_quorum_nonempty _ _ hqa) (by dsimp only; rw [hloc]; exact hpe)
    dsimp only at this
    rw [hloc, hpx] at this
    exact this
  unfold CoordinationState.isElectionQuorum VoteCollection.isQuorum
  rw [hcomm, hacc]
  unfold VoteCollection.isQuorum at hqc hqa
  rw [pv_quorum_mono _ _ _ hsub hqc, pv_quorum_mono _ _ _ hsub hqa]
  rfl

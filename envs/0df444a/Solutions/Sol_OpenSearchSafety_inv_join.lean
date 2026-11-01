-- Prove2me | solution 1 for OpenSearchSafety.inv_join
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:54:47.061295+00:00
-- url     : https://prove2.me/submissions/adeb1254-b0f8-469c-aa5e-29349333488d

import Definitions.Def_OpenSearchSafety
import Theorems.Thm_OpenSearchSafety_descends_trans
import Theorems.Thm_OpenSearchSafety_inv_descends_key
import Theorems.Thm_OpenSearchSafety_inv_descends_parent
import Theorems.Thm_OpenSearchSafety_inv_reign_first
import Theorems.Thm_OpenSearchSafety_inv_committed_published
import Theorems.Thm_OpenSearchSafety_inv_eligible_of_won
import Theorems.Thm_OpenSearchSafety_inv_won_of_electionWon
import Theorems.Thm_OpenSearchSafety_inv_election_unique

open OpenSearchCoordination OpenSearchSafety

private theorem set_node_self {V : Type} (W : Cluster V) (n : NodeId) (cs : CoordinationState V) :
    (W.set n cs).node n = cs := by
  simp [Cluster.set]

private theorem set_node_ne {V : Type} (W : Cluster V) (n m : NodeId) (cs : CoordinationState V) (h : m ≠ n) :
    (W.set n cs).node m = W.node m := by
  simp [Cluster.set, h]

private theorem set_sent {V : Type} (W : Cluster V) (n : NodeId) (cs : CoordinationState V) :
    (W.set n cs).sent = W.sent := rfl

private theorem send_node {V : Type} (W : Cluster V) (m : Message V) : (W.send m).node = W.node := rfl

private theorem send_sent {V : Type} (W : Cluster V) (m x : Message V) :
    (W.send m).sent x ↔ W.sent x ∨ x = m := Iff.rfl

private theorem committed_mono {V : Type} {W W' : Cluster V} (hg : ∀ m, W.sent m → W'.sent m) {t : Nat} {v : Int}
    (h : Committed W t v) : Committed W' t v := by
  obtain ⟨src, h⟩ := h
  exact ⟨src, hg _ h⟩

private theorem published_mono {V : Type} {W W' : Cluster V} (hg : ∀ m, W.sent m → W'.sent m) {t : Nat} {v : Int}
    (h : Published W t v) : Published W' t v := by
  obtain ⟨src, s, pt, pv, hs, h1, h2⟩ := h
  exact ⟨src, s, pt, pv, hg _ hs, h1, h2⟩

private theorem parent_mono {V : Type} {W W' : Cluster V} (hg : ∀ m, W.sent m → W'.sent m) {t t' : Nat}
    {v v' : Int} (h : Parent W t v t' v') : Parent W' t v t' v' := by
  obtain ⟨src, s, hs, h1, h2⟩ := h
  exact ⟨src, s, hg _ hs, h1, h2⟩

private theorem descends_mono {V : Type} {W W' : Cluster V} (hg : ∀ m, W.sent m → W'.sent m) {t t' : Nat}
    {v v' : Int} (h : Descends W t v t' v') : Descends W' t v t' v' := by
  induction h with
  | refl => exact .refl _ _
  | step _ _ _ _ _ hp ih => exact .step _ _ _ _ _ _ ih (parent_mono hg hp)

private theorem realizes_mono {V : Type} {P : Params} {W W' : Cluster V} (hg : ∀ m, W.sent m → W'.sent m)
    {t : Nat} {v : Int} {x y : VotingConfiguration} (h : Realizes P W t v x y) : Realizes P W' t v x y := by
  rcases h with h | ⟨src, s, pt, pv, hs, h1, h2, h3, h4⟩
  · exact Or.inl h
  · exact Or.inr ⟨src, s, pt, pv, hg _ hs, h1, h2, h3, h4.imp id (fun h => ⟨h.1, committed_mono hg h.2⟩)⟩

private theorem joinVoters_mono {V : Type} {P : Params} {W W' : Cluster V} (hg : ∀ m, W.sent m → W'.sent m)
    {L : NodeId} {t : Nat} {J : List NodeId} (h : JoinVoters P W L t J) : JoinVoters P W' L t J := by
  intro x hx
  obtain ⟨he, j, hj, h1⟩ := h x hx
  exact ⟨he, j, hg _ hj, h1⟩

private theorem baseVoters_mono {V : Type} {P : Params} {W W' : Cluster V} (hg : ∀ m, W.sent m → W'.sent m)
    {L : NodeId} {t bt : Nat} {bv : Int} {J : List NodeId} (h : BaseVoters P W L t bt bv J) :
    BaseVoters P W' L t bt bv J := by
  intro x hx
  obtain ⟨he, j, hj, h1⟩ := h x hx
  exact ⟨he, j, hg _ hj, h1⟩

private theorem respVoters_mono {V : Type} {P : Params} {W W' : Cluster V} (hg : ∀ m, W.sent m → W'.sent m)
    {t : Nat} {v : Int} {A : List NodeId} (h : RespVoters P W t v A) : RespVoters P W' t v A := by
  intro x hx
  obtain ⟨he, d, hd⟩ := h x hx
  exact ⟨he, d, hg _ hd⟩

private theorem electionRecord_mono {V : Type} {P : Params} {W W' : Cluster V} (hg : ∀ m, W.sent m → W'.sent m)
    {L : NodeId} {t bt : Nat} {bv : Int} {x y : VotingConfiguration} {J : List NodeId}
    (h : ElectionRecord P W L t bt bv x y J) : ElectionRecord P W' L t bt bv x y J := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, realizes_mono hg h2, baseVoters_mono hg h3, h4, h5⟩

private theorem filter_length_add_le {α : Type} (L : List α) (p q : α → Bool) :
    (L.filter p).length + (L.filter q).length ≤ L.length + (L.filter (fun x => p x && q x)).length := by
  induction L with
  | nil => simp
  | cons y ys ih =>
    cases hp : p y <;> cases hq : q y <;> simp [hp, hq] <;> omega

/-- Two quorums of the same voting configuration share a member of the configuration. -/
private theorem quorum_intersect (c : VotingConfiguration) (a b : List NodeId)
    (ha : c.hasQuorum a = true) (hb : c.hasQuorum b = true) :
    ∃ x, x ∈ c.nodeIds ∧ x ∈ a ∧ x ∈ b := by
  simp only [VotingConfiguration.hasQuorum, decide_eq_true_eq] at ha hb
  have key := filter_length_add_le c.nodeIds (fun x => a.contains x) (fun x => b.contains x)
  have hpos : 0 < (c.nodeIds.filter (fun x => a.contains x && b.contains x)).length := by omega
  obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos hpos
  rw [List.mem_filter, Bool.and_eq_true, List.contains_iff_mem, List.contains_iff_mem] at hx
  exact ⟨x, hx.1, hx.2.1, hx.2.2⟩

private theorem filter_length_mono {α : Type} (L : List α) (p q : α → Bool)
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
private theorem quorum_mono (c : VotingConfiguration) (a b : List NodeId) (hab : ∀ x, x ∈ a → x ∈ b)
    (ha : c.hasQuorum a = true) : c.hasQuorum b = true := by
  simp only [VotingConfiguration.hasQuorum, decide_eq_true_eq] at ha ⊢
  have := filter_length_mono c.nodeIds (fun x => a.contains x) (fun x => b.contains x)
    (fun x hx => by rw [List.contains_iff_mem] at hx ⊢; exact hab x hx)
  omega

/-- No configuration has a quorum of the empty list. -/
private theorem hasQuorum_nil (c : VotingConfiguration) : c.hasQuorum [] = false := by
  unfold VotingConfiguration.hasQuorum
  rw [decide_eq_false_iff_not]
  have : (c.nodeIds.filter (fun x => ([] : List NodeId).contains x)).length = 0 := by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]; simp
  omega

/-- An empty vote collection is a quorum of no configuration. -/
private theorem isQuorum_empty (c : VotingConfiguration) : VoteCollection.empty.isQuorum c = false :=
  hasQuorum_nil c

/-- The empty configuration has no quorum. -/
private theorem empty_no_quorum (a : List NodeId) : VotingConfiguration.EMPTY_CONFIG.hasQuorum a = false := by
  rfl

/-- A quorum is a nonempty list. -/
private theorem ne_nil_of_hasQuorum (c : VotingConfiguration) (a : List NodeId) (h : c.hasQuorum a = true) :
    a ≠ [] := by
  intro e
  rw [e, hasQuorum_nil] at h
  cases h

/-- Votes are only ever counted from cluster-manager-eligible nodes. -/
private theorem addVote_mem (v : VoteCollection) (n : DiscoveryNode) (x : NodeId) :
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

private theorem spec_setInitialState {V : Type} (cs : CoordinationState V) (s : ClusterState V)
    (cs' : CoordinationState V) (h : cs.setInitialState s = .ok cs') :
    cs.lastAcceptedConfiguration.isEmpty = true ∧ cs' = { cs with lastAcceptedState := s } := by
  unfold CoordinationState.setInitialState at h
  split at h
  · cases h
  · rename_i hne
    simp only [Except.ok.injEq] at h
    exact ⟨by simpa using hne, h.symm⟩

private theorem spec_startJoin {V : Type} (cs : CoordinationState V) (req : StartJoinRequest)
    (cs' : CoordinationState V) (j : Join) (h : cs.handleStartJoin req = .ok (cs', j)) :
    cs.currentTerm < req.term ∧
    cs' = { cs with currentTerm := req.term, lastPublishedVersion := 0,
                    lastPublishedConfiguration := cs.lastAcceptedConfiguration, startedJoinSinceLastReboot := true,
                    electionWon := false, joinVotes := VoteCollection.empty,
                    publishVotes := VoteCollection.empty } ∧
    j = ⟨cs.localNode, req.sourceNode, req.term, cs.lastAcceptedTerm, cs.lastAcceptedVersionOrMetadataVersion⟩ := by
  unfold CoordinationState.handleStartJoin at h
  split at h
  · cases h
  · rename_i hlt
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, rfl, rfl⟩

private theorem spec_join {V : Type} (es : ElectionStrategy) (cs : CoordinationState V) (j : Join)
    (cs' : CoordinationState V) (b : Bool) (h : cs.handleJoin es j = .ok (cs', b)) :
    j.term = cs.currentTerm ∧ cs.startedJoinSinceLastReboot = true ∧
    cs.lastAcceptedConfiguration.isEmpty = false ∧
    (j.lastAcceptedTerm < cs.lastAcceptedTerm ∨
      (j.lastAcceptedTerm = cs.lastAcceptedTerm ∧ j.lastAcceptedVersion ≤ cs.lastAcceptedVersionOrMetadataVersion)) ∧
    cs' = { cs with joinVotes := (cs.joinVotes.addVote j.sourceNode).1,
                    electionWon := cs.isElectionQuorum es (cs.joinVotes.addVote j.sourceNode).1,
                    lastPublishedVersion :=
                      if cs.isElectionQuorum es (cs.joinVotes.addVote j.sourceNode).1 = true ∧
                          cs.electionWon = false
                      then cs.lastAcceptedVersion else cs.lastPublishedVersion } := by
  unfold CoordinationState.handleJoin at h
  split at h
  · cases h
  rename_i h1
  split at h
  · cases h
  rename_i h2
  split at h
  · cases h
  rename_i h3
  split at h
  · cases h
  rename_i h4
  split at h
  · cases h
  rename_i h5
  have hlex : j.lastAcceptedTerm < cs.lastAcceptedTerm ∨
      (j.lastAcceptedTerm = cs.lastAcceptedTerm ∧ j.lastAcceptedVersion ≤ cs.lastAcceptedVersionOrMetadataVersion) := by
    by_cases ht : j.lastAcceptedTerm = cs.lastAcceptedTerm
    · exact Or.inr ⟨ht, by have := fun hv => h4 ⟨ht, hv⟩; omega⟩
    · exact Or.inl (by omega)
  have h1' : j.term = cs.currentTerm := Classical.not_not.mp h1
  have h2' : cs.startedJoinSinceLastReboot = true := by simpa using h2
  have h5' : cs.lastAcceptedConfiguration.isEmpty = false := by simpa using h5
  refine ⟨h1', h2', h5', hlex, ?_⟩
  generalize hva : cs.joinVotes.addVote j.sourceNode = va at h ⊢
  obtain ⟨votes, added⟩ := va
  dsimp only at h ⊢
  split at h
  · rename_i hw
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [Bool.and_eq_true, Bool.not_eq_true'] at hw
    simp [hw]
  · rename_i hw
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [Bool.and_eq_true, Bool.not_eq_true'] at hw
    have : ¬ (cs.isElectionQuorum es votes = true ∧ cs.electionWon = false) := hw
    simp only [this, if_false]

private theorem spec_clientValue {V : Type} (cs : CoordinationState V) (s : ClusterState V)
    (cs' : CoordinationState V) (p : PublishRequest V) (h : cs.handleClientValue s = .ok (cs', p)) :
    cs.electionWon = true ∧ cs.lastPublishedVersion = cs.lastAcceptedVersion ∧ s.term = cs.currentTerm ∧
    cs.lastAcceptedVersion < s.version ∧
    (s.lastAcceptedConfiguration = cs.lastAcceptedConfiguration ∨
      cs.lastCommittedConfiguration = cs.lastAcceptedConfiguration) ∧
    cs.joinVotes.isQuorum s.lastAcceptedConfiguration = true ∧
    p = ⟨s⟩ ∧ cs' = { cs with lastPublishedVersion := s.version,
                               lastPublishedConfiguration := s.lastAcceptedConfiguration,
                               publishVotes := VoteCollection.empty } := by
  unfold CoordinationState.handleClientValue at h
  split at h
  · cases h
  rename_i h1
  split at h
  · cases h
  rename_i h2
  split at h
  · cases h
  rename_i h3
  split at h
  · cases h
  rename_i h4
  split at h
  · cases h
  rename_i h5
  split at h
  · cases h
  rename_i h6
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have h2' : cs.lastPublishedVersion = cs.lastAcceptedVersion := Classical.not_not.mp h2
  refine ⟨by simpa using h1, h2', Classical.not_not.mp h3, by omega, ?_, by simpa using h6, rfl, rfl⟩
  by_cases hx : s.lastAcceptedConfiguration = cs.lastAcceptedConfiguration
  · exact Or.inl hx
  · exact Or.inr (Classical.not_not.mp (fun hy => h5 ⟨hx, hy⟩))

private theorem spec_publish {V : Type} (cs : CoordinationState V) (req : PublishRequest V)
    (cs' : CoordinationState V) (resp : PublishResponse) (h : cs.handlePublishRequest req = .ok (cs', resp)) :
    req.acceptedState.term = cs.currentTerm ∧
    (req.acceptedState.term = 0 ∨
      ¬ (req.acceptedState.term = cs.lastAcceptedTerm ∧ req.acceptedState.version ≤ cs.lastAcceptedVersion)) ∧
    resp = ⟨req.acceptedState.term, req.acceptedState.version⟩ ∧
    cs' = { cs with lastAcceptedState := req.acceptedState } := by
  unfold CoordinationState.handlePublishRequest at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hterm
    have hterm' : req.acceptedState.term = cs.currentTerm := Classical.not_not.mp hterm
    split at h
    · split at h
      · rename_i hzen
        split at h
        · cases h
        · split at h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨hterm', Or.inl hzen, rfl, rfl⟩
          · cases h
      · cases h
    · rename_i hnle
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hterm', Or.inr hnle, rfl, rfl⟩

private theorem spec_respond {V : Type} (cs : CoordinationState V) (src : DiscoveryNode) (r : PublishResponse)
    (cs' : CoordinationState V) (o : Option ApplyCommitRequest) (h : cs.handlePublishResponse src r = .ok (cs', o)) :
    cs.electionWon = true ∧ r.term = cs.currentTerm ∧ r.version = cs.lastPublishedVersion ∧
    cs' = { cs with publishVotes := (cs.publishVotes.addVote src).1 } ∧
    (∀ c, o = some c →
      c = ⟨cs.localNode, cs.currentTerm, cs.lastPublishedVersion⟩ ∧
      cs'.publishVotes.isQuorum cs.lastCommittedConfiguration = true ∧
      cs'.publishVotes.isQuorum cs.lastPublishedConfiguration = true) := by
  unfold CoordinationState.handlePublishResponse at h
  split at h
  · cases h
  rename_i h1
  split at h
  · cases h
  rename_i h2
  split at h
  · cases h
  rename_i h3
  have h1' : cs.electionWon = true := by simpa using h1
  have h2' : r.term = cs.currentTerm := Classical.not_not.mp h2
  have h3' : r.version = cs.lastPublishedVersion := Classical.not_not.mp h3
  dsimp only at h
  split at h
  · rename_i hq
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨h1', h2', h3', rfl, ?_⟩
    intro c hc
    cases hc
    unfold CoordinationState.isPublishQuorum at hq
    rw [Bool.and_eq_true] at hq
    exact ⟨by rw [h2', h3'], hq.1, hq.2⟩
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨h1', h2', h3', rfl, ?_⟩
    intro c hc
    cases hc

private theorem spec_commit {V : Type} (cs : CoordinationState V) (c : ApplyCommitRequest) (cs' : CoordinationState V)
    (h : cs.handleCommit c = .ok cs') :
    c.term = cs.currentTerm ∧ c.term = cs.lastAcceptedTerm ∧ c.version = cs.lastAcceptedVersion ∧
    cs' = { cs with lastAcceptedState := cs.lastAcceptedState.markCommitted } := by
  unfold CoordinationState.handleCommit at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i h1 h2 h3
        simp only [Except.ok.injEq] at h
        exact ⟨Classical.not_not.mp h1, Classical.not_not.mp h2, Classical.not_not.mp h3, h.symm⟩

/-- `markCommitted` keeps the term, the version and the last accepted configuration, and makes the last committed
configuration the last accepted one. -/
private theorem markCommitted_spec {V : Type} (s : ClusterState V) :
    s.markCommitted.term = s.term ∧ s.markCommitted.version = s.version ∧
    s.markCommitted.lastAcceptedConfiguration = s.lastAcceptedConfiguration ∧
    s.markCommitted.lastCommittedConfiguration = s.lastAcceptedConfiguration := by
  unfold ClusterState.markCommitted
  dsimp only
  split <;> split <;> simp_all

/-- At a term ≥ 1, `versionOrMetadataVersion` is the version. -/
private theorem vomv_of_pos {V : Type} (cs : CoordinationState V) (h : cs.lastAcceptedTerm ≠ 0) :
    cs.lastAcceptedVersionOrMetadataVersion = cs.lastAcceptedVersion := by
  unfold CoordinationState.lastAcceptedVersionOrMetadataVersion ClusterState.versionOrMetadataVersion
  split
  · rename_i hc; exact absurd hc h
  · rfl

/-- `join` preserves the invariant. The only hard case is an election win: no publication of the term exists and no
other node has won it, by `inv_election_unique` (two election records of a term have the same candidate), applied to
the winner's new record and to the first publication of the term or the other winner's record. -/
theorem solution {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hinv : Inv P W)
    (n : NodeId) (j : Join) (cs' : CoordinationState V) (b : Bool) (hsent : W.sent (.join j))
    (hdest : j.targetNode.id = n) (h : (W.node n).handleJoin P.strategy j = .ok (cs', b)) :
    Inv P (W.set n cs') := by
  obtain ⟨hjt, hsj, hlacne, hguard, hcs⟩ := spec_join _ _ _ _ _ h
  clear h
  generalize hvotes : ((W.node n).joinVotes.addVote j.sourceNode).1 = votes at hcs
  generalize hwon : (W.node n).isElectionQuorum P.strategy votes = won at hcs
  have e_ln : cs'.localNode = (W.node n).localNode := by rw [hcs]
  have e_ct : cs'.currentTerm = (W.node n).currentTerm := by rw [hcs]
  have e_ew : cs'.electionWon = won := by rw [hcs]
  have e_jv : cs'.joinVotes = votes := by rw [hcs]
  have e_pv : cs'.publishVotes = (W.node n).publishVotes := by rw [hcs]
  have e_sj : cs'.startedJoinSinceLastReboot = (W.node n).startedJoinSinceLastReboot := by rw [hcs]
  have e_lpv : cs'.lastPublishedVersion = if won = true ∧ (W.node n).electionWon = false then
      (W.node n).lastAcceptedVersion else (W.node n).lastPublishedVersion := by rw [hcs]
  have e_lpc : cs'.lastPublishedConfiguration = (W.node n).lastPublishedConfiguration := by rw [hcs]
  have e_lat : cs'.lastAcceptedTerm = (W.node n).lastAcceptedTerm := by rw [hcs]; rfl
  have e_lav : cs'.lastAcceptedVersion = (W.node n).lastAcceptedVersion := by rw [hcs]; rfl
  have e_lcc : cs'.lastCommittedConfiguration = (W.node n).lastCommittedConfiguration := by rw [hcs]; rfl
  have e_lac : cs'.lastAcceptedConfiguration = (W.node n).lastAcceptedConfiguration := by rw [hcs]; rfl
  clear hcs
  have hg : ∀ m, W.sent m → (W.set n cs').sent m := fun _ h => h
  have hne : P.eligible n = true := by have := (hinv.join_wf j hsent).2; rwa [hdest] at this
  have hjel : j.sourceNode.isClusterManagerNode = P.eligible j.sourceNode.id :=
    congrArg DiscoveryNode.isClusterManagerNode (hinv.join_wf j hsent).1
  -- the votes are the old ones and the new voter, if eligible
  have hmem : ∀ x, x ∈ votes.nodes →
      x ∈ (W.node n).joinVotes.nodes ∨ (x = j.sourceNode.id ∧ P.eligible x = true) := by
    intro x hx
    rw [← hvotes, addVote_mem] at hx
    rcases hx with hx | ⟨rfl, hc⟩
    · exact Or.inl hx
    · exact Or.inr ⟨rfl, hjel ▸ hc⟩
  have hsub : ∀ x, x ∈ (W.node n).joinVotes.nodes → x ∈ votes.nodes := by
    intro x hx; rw [← hvotes, addVote_mem]; exact Or.inl hx
  have hbelow : Below j.lastAcceptedTerm j.lastAcceptedVersion (W.node n).lastAcceptedTerm
      (W.node n).lastAcceptedVersion := by
    rcases hguard with hlt | ⟨heq, hle⟩
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      by_cases h0 : (W.node n).lastAcceptedTerm = 0
      · exact Or.inl h0
      · right; rw [vomv_of_pos _ h0] at hle; exact hle
  have hvotes_sent : ∀ x, x ∈ votes.nodes → P.eligible x = true ∧ ∃ j' : Join, W.sent (.join j') ∧
      j'.sourceNode.id = x ∧ j'.targetNode.id = n ∧ j'.term = (W.node n).currentTerm ∧
      Below j'.lastAcceptedTerm j'.lastAcceptedVersion (W.node n).lastAcceptedTerm (W.node n).lastAcceptedVersion := by
    intro x hx
    rcases hmem x hx with hx | ⟨rfl, he⟩
    · exact hinv.joinVotes_sent n x hx
    · exact ⟨he, j, hsent, rfl, hdest, hjt, hbelow⟩
  have hwq : won = true ↔ (votes.isQuorum (W.node n).lastCommittedConfiguration = true ∧
      votes.isQuorum (W.node n).lastAcceptedConfiguration = true) := by
    rw [← hwon, hes]
    simp [CoordinationState.isElectionQuorum, ElectionStrategy.DEFAULT_INSTANCE]
  have hmono : (W.node n).electionWon = true → won = true := by
    intro hw
    obtain ⟨h1, h2⟩ := hinv.won_quorum n hw
    exact hwq.mpr ⟨quorum_mono _ _ _ hsub h1, quorum_mono _ _ _ hsub h2⟩
  have hctpos : 1 ≤ (W.node n).currentTerm := hinv.started_term_pos n hsj
  /- An election win: the node's accepted state is of an older term, no publication of the term exists, and no other
  node has won the term. -/
  have hnot_t : won = true → (W.node n).electionWon = false →
      (W.node n).lastAcceptedTerm ≠ (W.node n).currentTerm := by
    intro hw hew0 heq
    obtain ⟨-, hq⟩ := hwq.mp hw
    rcases hinv.accepted_realizes n hne with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨src₂, s₂, pt₂, pv₂, hs₂, h1, -, h3, -⟩
    · omega
    · omega
    · obtain ⟨J, hJ, -, hJq⟩ := hinv.pub_voters src₂ s₂ pt₂ pv₂ hs₂
      have hq' : s₂.lastAcceptedConfiguration.hasQuorum votes.nodes = true := by rw [← h3]; exact hq
      obtain ⟨x, -, hx1, hx2⟩ := quorum_intersect _ _ _ hq' hJq
      obtain ⟨hxe, j₁, hj₁, hs₁, ht₁, hterm₁, -⟩ := hvotes_sent x hx1
      obtain ⟨-, j₂, hj₂, hs₂', ht₂, hterm₂⟩ := hJ x hx2
      have hjj := hinv.join_unique j₁ j₂ hj₁ hj₂ (by rw [hs₁]; exact hxe) (hs₁.trans hs₂'.symm)
        (by rw [hterm₁, hterm₂, h1, heq])
      have hLn : src₂ = n := by rw [← ht₂, ← hjj, ht₁]
      subst hLn
      rcases hinv.pub_source_term src₂ s₂ pt₂ pv₂ hs₂ with hlt | ⟨-, hw' | hsj'⟩
      · rw [h1, heq] at hlt; omega
      · rw [hw'] at hew0; cases hew0
      · rw [hsj] at hsj'; cases hsj'
  have hrec_n : won = true → (W.node n).electionWon = false →
      ElectionRecord P W n (W.node n).currentTerm (W.node n).lastAcceptedTerm (W.node n).lastAcceptedVersion
        (W.node n).lastCommittedConfiguration (W.node n).lastAcceptedConfiguration votes.nodes := by
    intro hw hew0
    obtain ⟨hq1, hq2⟩ := hwq.mp hw
    refine ⟨Nat.lt_of_le_of_ne (hinv.term_le n hne) (hnot_t hw hew0), ?_, hvotes_sent, hq1, hq2⟩
    rcases hinv.accepted_realizes n hne with ⟨-, -, h0⟩ | hr
    · rw [h0] at hlacne
      simp [VotingConfiguration.isEmpty, VotingConfiguration.EMPTY_CONFIG] at hlacne
    · exact hr
  have hno_pub : won = true → (W.node n).electionWon = false →
      ∀ src s pt pv, W.sent (.publishRequest src s pt pv) → s.term ≠ (W.node n).currentTerm := by
    intro hw hew0 src s pt pv hs hst
    obtain ⟨L, F, pt', pv', hF, hFt, hFpt, -⟩ := inv_reign_first P W hinv src s pt pv hs
    obtain ⟨y, J, hFrec⟩ := hinv.pub_election L F pt' pv' hF hFpt
    rw [hFt, hst] at hFrec
    have hLn := inv_election_unique P hP W hinv _ L n _ _ _ _ _ _ _ _ _ _ hFrec (hrec_n hw hew0)
    subst hLn
    rcases hinv.pub_source_term L F pt' pv' hF with hlt' | ⟨-, hw' | hsj'⟩
    · rw [hFt, hst] at hlt'; omega
    · rw [hw'] at hew0; cases hew0
    · rw [hsj] at hsj'; cases hsj'
  have hno_other : won = true → (W.node n).electionWon = false →
      ∀ m, m ≠ n → (W.node m).electionWon = true → (W.node m).currentTerm ≠ (W.node n).currentTerm := by
    intro hw hew0 m hm hwm hct
    have hme := inv_eligible_of_won P W hinv m hwm
    have hmpos := hinv.started_term_pos m (hinv.won_started m hwm)
    by_cases hlv : (W.node m).lastPublishedVersion = (W.node m).lastAcceptedVersion
    · rcases hinv.leader_settled m hwm hlv with ⟨hlt, -⟩ | ⟨hlt, -⟩
      · rcases hinv.accepted_realizes m hme with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨src₂, s₂, pt₂, pv₂, hs₂, h1, -⟩
        · omega
        · omega
        · exact hno_pub hw hew0 _ _ _ _ hs₂ (by rw [h1, hlt, hct])
      · obtain ⟨hq1, hq2⟩ := hinv.won_quorum m hwm
        have hrec_m : ElectionRecord P W m (W.node n).currentTerm (W.node m).lastAcceptedTerm
            (W.node m).lastAcceptedVersion (W.node m).lastCommittedConfiguration
            (W.node m).lastAcceptedConfiguration (W.node m).joinVotes.nodes := by
          refine ⟨by rw [← hct]; exact hlt, ?_, ?_, hq1, hq2⟩
          · rcases hinv.accepted_realizes m hme with ⟨-, -, h0⟩ | hr
            · unfold VoteCollection.isQuorum at hq2
              rw [h0, empty_no_quorum] at hq2
              cases hq2
            · exact hr
          · intro x hx
            obtain ⟨he, j', hj', h1, h2, h3, h4⟩ := hinv.joinVotes_sent m x hx
            exact ⟨he, j', hj', h1, h2, by rw [h3, hct], h4⟩
        exact hm (inv_election_unique P hP W hinv _ m n _ _ _ _ _ _ _ _ _ _ hrec_m (hrec_n hw hew0))
    · obtain ⟨s, hs, h1, -⟩ := hinv.leader_inflight m hwm hlv
      exact hno_pub hw hew0 _ _ _ _ hs (by rw [h1, hct])
  -- nobody had won the term before
  have hwon_new : won = true → (W.node n).electionWon = false → ∀ a, ¬ Won P W a (W.node n).currentTerm := by
    rintro hw hew0 a ⟨-, ⟨hwa, hcta⟩ | ⟨s, pt, pv, hs, hst⟩⟩
    · by_cases ha : a = n
      · subst ha; rw [hew0] at hwa; cases hwa
      · exact hno_other hw hew0 a ha hwa hcta
    · exact hno_pub hw hew0 _ _ _ _ hs hst
  have hwonW' : ∀ a t', Won P (W.set n cs') a t' → Won P W a t' ∨
      (a = n ∧ t' = (W.node n).currentTerm ∧ won = true ∧ (W.node n).electionWon = false) := by
    rintro a t' ⟨he, ⟨hwa, hcta⟩ | hp⟩
    · by_cases ha : a = n
      · subst ha
        rw [set_node_self, e_ew] at hwa
        rw [set_node_self, e_ct] at hcta
        by_cases hew : (W.node a).electionWon = true
        · exact Or.inl ⟨he, Or.inl ⟨hew, hcta⟩⟩
        · exact Or.inr ⟨rfl, hcta.symm, hwa, by simpa using hew⟩
      · rw [set_node_ne _ _ _ _ ha] at hwa hcta; exact Or.inl ⟨he, Or.inl ⟨hwa, hcta⟩⟩
    · exact Or.inl ⟨he, Or.inr hp⟩
  -- without a new win, the node's election state is unchanged
  have hold : ¬ (won = true ∧ (W.node n).electionWon = false) → won = true → (W.node n).electionWon = true := by
    intro hnew hw
    cases hew : (W.node n).electionWon
    · exact absurd ⟨hw, hew⟩ hnew
    · rfl
  refine
    { localNode_eq := ?_, idle_of_not_won := ?_, won_started := ?_, votes_started := ?_, started_term_pos := ?_,
      won_quorum := ?_, not_won_no_quorum := ?_, joinVotes_sent := ?_, publishVotes_sent := ?_, term_le := ?_,
      accepted_realizes := ?_, join_wf := hinv.join_wf, join_term_le := ?_, join_unique := hinv.join_unique,
      join_after_response := hinv.join_after_response, response_le := ?_,
      response_published := hinv.response_published, pub_wf := hinv.pub_wf, pub_parent := hinv.pub_parent,
      pub_unique := hinv.pub_unique, pub_rooted := ?_, pub_same_term := ?_, pub_voters := hinv.pub_voters,
      pub_election := hinv.pub_election, commit_quorum := hinv.commit_quorum, won_unique := ?_,
      pub_source_term := ?_, leader_pubs := ?_, leader_inflight := ?_, leader_settled := ?_ }
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ln]; exact hinv.localNode_eq m
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.localNode_eq m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew, e_lpv, e_pv]
      intro hw0
      have hnew : ¬ (won = true ∧ (W.node m).electionWon = false) := fun h => by rw [hw0] at h; cases h.1
      rw [if_neg hnew]
      have hew0 : (W.node m).electionWon = false := by
        cases hew : (W.node m).electionWon
        · rfl
        · rw [hmono hew] at hw0; cases hw0
      exact hinv.idle_of_not_won m hew0
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.idle_of_not_won m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_sj]; intro _; exact hsj
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.won_started m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_sj]; intro _; exact hsj
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.votes_started m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_sj, e_ct]; exact hinv.started_term_pos m
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.started_term_pos m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew, e_jv, e_lcc, e_lac]; exact hwq.mp
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.won_quorum m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew, e_jv, e_lcc, e_lac]
      intro hw0 hq
      rw [hwq.mpr hq] at hw0
      cases hw0
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.not_won_no_quorum m
  · intro m x
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_jv, e_ct, e_lat, e_lav]; exact hvotes_sent x
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.joinVotes_sent m x
  · intro m x
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_pv, e_ct, e_lpv]
      intro hx
      by_cases hnew : won = true ∧ (W.node m).electionWon = false
      · rw [(hinv.idle_of_not_won m hnew.2).2] at hx; cases hx
      · rw [if_neg hnew]; exact hinv.publishVotes_sent m x hx
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.publishVotes_sent m x
  · intro m hme
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_lat, e_ct]; exact hinv.term_le m hme
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.term_le m hme
  · intro m hme
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_lat, e_lav, e_lcc, e_lac]
      exact (hinv.accepted_realizes m hme).imp id (realizes_mono hg)
    · rw [set_node_ne _ _ _ _ hm]; exact (hinv.accepted_realizes m hme).imp id (realizes_mono hg)
  · intro j' hj' hje
    by_cases hm : j'.sourceNode.id = n
    · rw [hm, set_node_self, e_ct]; have := hinv.join_term_le j' hj' hje; rw [hm] at this; exact this
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.join_term_le j' hj' hje
  · intro a d r hr ha
    by_cases hm : a = n
    · subst hm; rw [set_node_self, e_ct, e_lat, e_lav]; exact hinv.response_le a d r hr ha
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.response_le a d r hr ha
  · intro src s pt pv hs
    obtain ⟨v₀, h⟩ := hinv.pub_rooted src s pt pv hs
    exact ⟨v₀, descends_mono hg h⟩
  · intro src s pt pv src' s' pt' pv' hs hs' ht
    exact (hinv.pub_same_term src s pt pv src' s' pt' pv' hs hs' ht).imp (descends_mono hg) (descends_mono hg)
  · intro a b' t' ha hb
    rcases hwonW' a t' ha with ha' | ⟨han, hta, hw, hew0⟩
    · rcases hwonW' b' t' hb with hb' | ⟨-, htb, hw', hew0'⟩
      · exact hinv.won_unique a b' t' ha' hb'
      · rw [htb] at ha'; exact absurd ha' (hwon_new hw' hew0' a)
    · rcases hwonW' b' t' hb with hb' | ⟨hbn, -, -, -⟩
      · rw [hta] at hb'; exact absurd hb' (hwon_new hw hew0 b')
      · rw [han, hbn]
  · intro src s pt pv hs
    by_cases hm : src = n
    · subst hm; rw [set_node_self, e_ct, e_ew, e_sj]
      rcases hinv.pub_source_term src s pt pv hs with h | ⟨h1, hw | hsj'⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, Or.inl (hmono hw)⟩
      · exact Or.inr ⟨h1, Or.inr hsj'⟩
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.pub_source_term src s pt pv hs
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew, e_ct, e_lpv, e_jv]
      intro hw src s pt pv hs ht
      by_cases hnew : won = true ∧ (W.node m).electionWon = false
      · exact absurd ht (hno_pub hnew.1 hnew.2 _ _ _ _ hs)
      · rw [if_neg hnew]
        obtain ⟨h1, h2, h3, h4⟩ := hinv.leader_pubs m (hold hnew hw) src s pt pv hs ht
        exact ⟨h1, descends_mono hg h2, quorum_mono _ _ _ hsub h3, quorum_mono _ _ _ hsub h4⟩
    · rw [set_node_ne _ _ _ _ hm]
      intro hw src s pt pv hs ht
      obtain ⟨h1, h2, h3, h4⟩ := hinv.leader_pubs m hw src s pt pv hs ht
      exact ⟨h1, descends_mono hg h2, h3, h4⟩
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew, e_lpv, e_lav, e_lat, e_ct, e_lpc, e_lcc, e_lac]
      intro hw hne'
      by_cases hnew : won = true ∧ (W.node m).electionWon = false
      · rw [if_pos hnew] at hne'; exact absurd rfl hne'
      · rw [if_neg hnew] at hne' ⊢
        exact hinv.leader_inflight m (hold hnew hw) hne'
    · rw [set_node_ne _ _ _ _ hm]
      intro hw hne'
      obtain ⟨s, hs, h1, h2, h3, h4⟩ := hinv.leader_inflight m hw hne'
      exact ⟨s, hs, h1, h2, h3, h4.imp id (fun h => ⟨h.1, committed_mono hg h.2.1, h.2.2⟩)⟩
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew, e_lpv, e_lav, e_lat, e_ct, e_lpc, e_lac]
      intro hw hv
      by_cases hnew : won = true ∧ (W.node m).electionWon = false
      · exact Or.inr ⟨Nat.lt_of_le_of_ne (hinv.term_le m hne) (hnot_t hnew.1 hnew.2),
          fun src s pt pv hs => hno_pub hnew.1 hnew.2 src s pt pv hs⟩
      · rw [if_neg hnew] at hv
        exact hinv.leader_settled m (hold hnew hw) hv
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.leader_settled m

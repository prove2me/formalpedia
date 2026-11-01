-- Prove2me | solution 1 for OpenSearchSafety.inv_startJoin
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:54:46.48124+00:00
-- url     : https://prove2.me/submissions/7c6aeafc-79c0-4863-a65a-1f958c15a55c

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

/-- `startJoin` preserves the invariant. -/
theorem solution {V : Type} (P : Params) (_hP : P.InitCompatible)
    (_hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hinv : Inv P W)
    (n src : NodeId) (t : Nat) (cs' : CoordinationState V) (j : Join) (hsrc : P.eligible src = true)
    (h : (W.node n).handleStartJoin ⟨P.dn src, t⟩ = .ok (cs', j)) : Inv P ((W.set n cs').send (.join j)) := by
  obtain ⟨hlt, hcs, hj⟩ := spec_startJoin _ _ _ _ h
  have hlt : (W.node n).currentTerm < t := hlt
  have e_ln : cs'.localNode = (W.node n).localNode := by rw [hcs]
  have e_ct : cs'.currentTerm = t := by rw [hcs]
  have e_lat : cs'.lastAcceptedTerm = (W.node n).lastAcceptedTerm := by rw [hcs]; rfl
  have e_lav : cs'.lastAcceptedVersion = (W.node n).lastAcceptedVersion := by rw [hcs]; rfl
  have e_lcc : cs'.lastCommittedConfiguration = (W.node n).lastCommittedConfiguration := by rw [hcs]; rfl
  have e_lac : cs'.lastAcceptedConfiguration = (W.node n).lastAcceptedConfiguration := by rw [hcs]; rfl
  have e_ew : cs'.electionWon = false := by rw [hcs]
  have e_jv : cs'.joinVotes = VoteCollection.empty := by rw [hcs]
  have e_pv : cs'.publishVotes = VoteCollection.empty := by rw [hcs]
  have e_lpv : cs'.lastPublishedVersion = 0 := by rw [hcs]
  have j_src : j.sourceNode = P.dn n := by rw [hj, ← hinv.localNode_eq n]
  have j_srcid : j.sourceNode.id = n := by rw [j_src]; rfl
  have j_tgt : j.targetNode = P.dn src := by rw [hj]
  have j_term : j.term = t := by rw [hj]
  have j_lt : j.lastAcceptedTerm = (W.node n).lastAcceptedTerm := by rw [hj]
  have j_lv : j.lastAcceptedVersion = (W.node n).lastAcceptedVersionOrMetadataVersion := by rw [hj]
  clear hcs hj h
  -- the soup: one new join
  have hg : ∀ m, W.sent m → ((W.set n cs').send (.join j)).sent m := fun _ h => Or.inl h
  have hpr : ∀ src s pt pv, ((W.set n cs').send (.join j)).sent (.publishRequest src s pt pv) →
      W.sent (.publishRequest src s pt pv) := by
    intro _ _ _ _ h; rcases h with h | h
    · exact h
    · cases h
  have hrs : ∀ a d r, ((W.set n cs').send (.join j)).sent (.publishResponse a d r) →
      W.sent (.publishResponse a d r) := by
    intro _ _ _ h; rcases h with h | h
    · exact h
    · cases h
  have hac : ∀ c, ((W.set n cs').send (.join j)).sent (.applyCommit c) → W.sent (.applyCommit c) := by
    intro _ h; rcases h with h | h
    · exact h
    · cases h
  have hjn : ∀ j', ((W.set n cs').send (.join j)).sent (.join j') → W.sent (.join j') ∨ j' = j := by
    intro j' h; rcases h with h | h
    · exact Or.inl h
    · cases h; exact Or.inr rfl
  have hnode : ∀ m, m ≠ n → ((W.set n cs').send (.join j)).node m = W.node m :=
    fun m hm => set_node_ne _ _ _ _ hm
  have hnode_n : ((W.set n cs').send (.join j)).node n = cs' := set_node_self _ _ _
  -- every response has a term ≥ 1
  have hrpos : ∀ a d (r : PublishResponse), W.sent (.publishResponse a d r) → 1 ≤ r.term := by
    intro a d r hr
    obtain ⟨s, pt, pv, hs, hst, -⟩ := hinv.response_published a d r hr
    have := (hinv.pub_wf _ _ _ _ hs).2.1
    omega
  -- an eligible node's old joins are for terms below t
  have hold : ∀ j', W.sent (.join j') → j'.sourceNode.id = n → P.eligible n = true → j'.term < t := by
    intro j' hj' hs he
    have := hinv.join_term_le j' hj' (by rw [hs]; exact he)
    rw [hs] at this
    omega
  have hwon : ∀ a t', Won P ((W.set n cs').send (.join j)) a t' → Won P W a t' := by
    rintro a t' ⟨he, hw | ⟨s, pt, pv, hs, hst⟩⟩
    · by_cases ha : a = n
      · subst ha; rw [hnode_n, e_ew] at hw; cases hw.1
      · rw [hnode a ha] at hw; exact ⟨he, Or.inl hw⟩
    · exact ⟨he, Or.inr ⟨s, pt, pv, hpr _ _ _ _ hs, hst⟩⟩
  refine
    { localNode_eq := ?_, idle_of_not_won := ?_, won_started := ?_, votes_started := ?_, started_term_pos := ?_,
      won_quorum := ?_, not_won_no_quorum := ?_, joinVotes_sent := ?_, publishVotes_sent := ?_, term_le := ?_,
      accepted_realizes := ?_, join_wf := ?_, join_term_le := ?_, join_unique := ?_,
      join_after_response := ?_, response_le := ?_, response_published := ?_, pub_wf := ?_, pub_parent := ?_,
      pub_unique := ?_, pub_rooted := ?_, pub_same_term := ?_, pub_voters := ?_, pub_election := ?_,
      commit_quorum := ?_, won_unique := ?_, pub_source_term := ?_, leader_pubs := ?_, leader_inflight := ?_,
      leader_settled := ?_ }
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ln]; exact hinv.localNode_eq m
    · rw [hnode m hm]; exact hinv.localNode_eq m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_lpv, e_pv]; intro _; exact ⟨rfl, rfl⟩
    · rw [hnode m hm]; exact hinv.idle_of_not_won m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew]; intro h; cases h
    · rw [hnode m hm]; exact hinv.won_started m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_jv]; intro h; exact absurd rfl h
    · rw [hnode m hm]; exact hinv.votes_started m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ct]; intro _; omega
    · rw [hnode m hm]; exact hinv.started_term_pos m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew]; intro h; cases h
    · rw [hnode m hm]; exact hinv.won_quorum m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_jv, isQuorum_empty]; intro _ h; cases h.1
    · rw [hnode m hm]; exact hinv.not_won_no_quorum m
  · intro m x
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_jv]; intro h; cases h
    · rw [hnode m hm]
      intro hx
      obtain ⟨he, j', hj', h1⟩ := hinv.joinVotes_sent m x hx
      exact ⟨he, j', hg _ hj', h1⟩
  · intro m x
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_pv]; intro h; cases h
    · rw [hnode m hm]
      intro hx
      obtain ⟨he, h1⟩ := hinv.publishVotes_sent m x hx
      exact ⟨he, hg _ h1⟩
  · intro m hme
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ct, e_lat]; have := hinv.term_le m hme; omega
    · rw [hnode m hm]; exact hinv.term_le m hme
  · intro m hme
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_lat, e_lav, e_lcc, e_lac]
      exact (hinv.accepted_realizes m hme).imp id (realizes_mono hg)
    · rw [hnode m hm]; exact (hinv.accepted_realizes m hme).imp id (realizes_mono hg)
  · intro j' hj'
    rcases hjn j' hj' with hj' | rfl
    · exact hinv.join_wf j' hj'
    · rw [j_srcid, j_src, j_tgt]; exact ⟨rfl, hsrc⟩
  · intro j' hj' hje
    by_cases hm : j'.sourceNode.id = n
    · rw [hm, hnode_n, e_ct]
      rcases hjn j' hj' with hj' | rfl
      · exact Nat.le_of_lt (hold j' hj' hm (by rw [← hm]; exact hje))
      · rw [j_term]; exact Nat.le_refl _
    · rw [hnode _ hm]
      rcases hjn j' hj' with hj' | rfl
      · exact hinv.join_term_le j' hj' hje
      · exact absurd j_srcid hm
  · intro j₁ j₂ h₁ h₂ he hs ht
    rcases hjn j₁ h₁ with h₁' | rfl <;> rcases hjn j₂ h₂ with h₂' | rfl
    · exact hinv.join_unique j₁ j₂ h₁' h₂' he hs ht
    · rw [j_srcid] at hs; rw [hs] at he
      have := hold j₁ h₁' hs he
      omega
    · rw [j_srcid] at hs he
      have := hold j₂ h₂' hs.symm he
      omega
    · rfl
  · intro j' a d r hj' hr hs ha hrt
    have hr0 := hrs a d r hr
    rcases hjn j' hj' with hj0 | rfl
    · exact hinv.join_after_response j' a d r hj0 hr0 hs ha hrt
    · rw [j_srcid] at hs; subst hs
      obtain ⟨-, h2⟩ := hinv.response_le n d r hr0 ha
      have h1 := hrpos _ _ _ hr0
      rw [j_lt, j_lv]
      unfold KeyLE at h2 ⊢
      have hpos : (W.node n).lastAcceptedTerm ≠ 0 := by omega
      rw [vomv_of_pos _ hpos]
      exact h2
  · intro a d r hr ha
    have hr0 := hrs a d r hr
    by_cases hm : a = n
    · subst hm; rw [hnode_n, e_ct, e_lat, e_lav]
      obtain ⟨h1, h2⟩ := hinv.response_le a d r hr0 ha
      exact ⟨by omega, h2⟩
    · rw [hnode a hm]; exact hinv.response_le a d r hr0 ha
  · intro a d r hr
    obtain ⟨s, pt, pv, hs, h1, h2⟩ := hinv.response_published a d r (hrs a d r hr)
    exact ⟨s, pt, pv, hg _ hs, h1, h2⟩
  · intro src s pt pv hs; exact hinv.pub_wf src s pt pv (hpr _ _ _ _ hs)
  · intro src s pt pv hs hpt
    obtain ⟨src', s', pt', pv', hs', h1, h2, h3, h4⟩ := hinv.pub_parent src s pt pv (hpr _ _ _ _ hs) hpt
    exact ⟨src', s', pt', pv', hg _ hs', h1, h2, h3.imp id (fun h => ⟨h.1, committed_mono hg h.2⟩), h4⟩
  · intro src s pt pv src' s' pt' pv' hs hs'
    exact hinv.pub_unique src s pt pv src' s' pt' pv' (hpr _ _ _ _ hs) (hpr _ _ _ _ hs')
  · intro src s pt pv hs
    obtain ⟨v₀, h⟩ := hinv.pub_rooted src s pt pv (hpr _ _ _ _ hs)
    exact ⟨v₀, descends_mono hg h⟩
  · intro src s pt pv src' s' pt' pv' hs hs' ht
    exact (hinv.pub_same_term src s pt pv src' s' pt' pv' (hpr _ _ _ _ hs) (hpr _ _ _ _ hs') ht).imp
      (descends_mono hg) (descends_mono hg)
  · intro src s pt pv hs
    obtain ⟨J, h1, h2, h3⟩ := hinv.pub_voters src s pt pv (hpr _ _ _ _ hs)
    exact ⟨J, joinVoters_mono hg h1, h2, h3⟩
  · intro src s pt pv hs hpt
    obtain ⟨y, J, h1⟩ := hinv.pub_election src s pt pv (hpr _ _ _ _ hs) hpt
    exact ⟨y, J, electionRecord_mono hg h1⟩
  · intro c hc
    obtain ⟨src, s, pt, pv, hs, h1, h2, A, hA, h3, h4⟩ := hinv.commit_quorum c (hac c hc)
    refine ⟨src, s, pt, pv, hg _ hs, h1, h2, A, respVoters_mono hg hA, h3, ?_⟩
    rcases h4 with h4 | ⟨h4, src', s', pt', pv', hs', h5, h6, h7⟩
    · exact Or.inl h4
    · exact Or.inr ⟨committed_mono hg h4, src', s', pt', pv', hg _ hs', h5, h6, h7⟩
  · intro a b t' ha hb
    exact hinv.won_unique a b t' (hwon a t' ha) (hwon b t' hb)
  · intro src' s pt pv hs
    have hs0 := hpr _ _ _ _ hs
    by_cases hm : src' = n
    · subst hm; rw [hnode_n, e_ct]
      left
      rcases hinv.pub_source_term src' s pt pv hs0 with h | ⟨h, -⟩ <;> omega
    · rw [hnode src' hm]; exact hinv.pub_source_term src' s pt pv hs0
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew]; intro h; cases h
    · rw [hnode m hm]
      intro hw src s pt pv hs ht
      obtain ⟨h1, h2, h3, h4⟩ := hinv.leader_pubs m hw src s pt pv (hpr _ _ _ _ hs) ht
      exact ⟨h1, descends_mono hg h2, h3, h4⟩
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew]; intro h; cases h
    · rw [hnode m hm]
      intro hw hne
      obtain ⟨s, hs, h1, h2, h3, h4⟩ := hinv.leader_inflight m hw hne
      exact ⟨s, hg _ hs, h1, h2, h3, h4.imp id (fun h => ⟨h.1, committed_mono hg h.2.1, h.2.2⟩)⟩
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew]; intro h; cases h
    · rw [hnode m hm]
      intro hw hv
      rcases hinv.leader_settled m hw hv with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, fun src s pt pv hs => h2 src s pt pv (hpr _ _ _ _ hs)⟩

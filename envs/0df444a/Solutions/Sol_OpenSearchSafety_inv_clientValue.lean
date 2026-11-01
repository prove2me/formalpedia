-- Prove2me | solution 1 for OpenSearchSafety.inv_clientValue
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:54:47.539702+00:00
-- url     : https://prove2.me/submissions/89ffcb5d-90f7-44a5-b6e2-18c0e2b06277

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

/-- `clientValue` preserves the invariant. -/
theorem solution {V : Type} (P : Params) (_hP : P.InitCompatible)
    (_hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hinv : Inv P W)
    (n : NodeId) (s : ClusterState V) (cs' : CoordinationState V) (p : PublishRequest V)
    (hcontract : (W.node n).clientValueContract s) (h : (W.node n).handleClientValue s = .ok (cs', p)) :
    Inv P ((W.set n cs').send (.publishRequest n p.acceptedState (W.node n).lastAcceptedTerm
      (W.node n).lastAcceptedVersion)) := by
  obtain ⟨hew, hlpv, hst, hsv, hreconf, hq, rfl, hcs⟩ := spec_clientValue _ _ _ _ h
  clear h
  have hlcc : s.lastCommittedConfiguration = (W.node n).lastCommittedConfiguration := hcontract
  have e_ln : cs'.localNode = (W.node n).localNode := by rw [hcs]
  have e_ct : cs'.currentTerm = (W.node n).currentTerm := by rw [hcs]
  have e_ew : cs'.electionWon = (W.node n).electionWon := by rw [hcs]
  have e_jv : cs'.joinVotes = (W.node n).joinVotes := by rw [hcs]
  have e_pv : cs'.publishVotes = VoteCollection.empty := by rw [hcs]
  have e_sj : cs'.startedJoinSinceLastReboot = (W.node n).startedJoinSinceLastReboot := by rw [hcs]
  have e_lpv : cs'.lastPublishedVersion = s.version := by rw [hcs]
  have e_lpc : cs'.lastPublishedConfiguration = s.lastAcceptedConfiguration := by rw [hcs]
  have e_lat : cs'.lastAcceptedTerm = (W.node n).lastAcceptedTerm := by rw [hcs]; rfl
  have e_lav : cs'.lastAcceptedVersion = (W.node n).lastAcceptedVersion := by rw [hcs]; rfl
  have e_lcc : cs'.lastCommittedConfiguration = (W.node n).lastCommittedConfiguration := by rw [hcs]; rfl
  have e_lac : cs'.lastAcceptedConfiguration = (W.node n).lastAcceptedConfiguration := by rw [hcs]; rfl
  clear hcs
  have hne : P.eligible n = true := inv_eligible_of_won P W hinv n hew
  have hctpos : 1 ≤ (W.node n).currentTerm := hinv.started_term_pos n (hinv.won_started n hew)
  obtain ⟨hq1, hq2⟩ := hinv.won_quorum n hew
  -- the leader's accepted state realizes its key
  have hreal : Realizes P W (W.node n).lastAcceptedTerm (W.node n).lastAcceptedVersion
      (W.node n).lastCommittedConfiguration (W.node n).lastAcceptedConfiguration := by
    rcases hinv.accepted_realizes n hne with ⟨-, -, h0⟩ | hr
    · unfold VoteCollection.isQuorum at hq2
      rw [h0, empty_no_quorum] at hq2
      cases hq2
    · exact hr
  -- the soup: one new publication, of term `t` = the current term, on top of the accepted key `(lat, lav)`
  generalize hW' : (W.set n cs').send (.publishRequest n s (W.node n).lastAcceptedTerm
    (W.node n).lastAcceptedVersion) = W'
  have hg : ∀ m, W.sent m → W'.sent m := fun _ h => by rw [← hW']; exact Or.inl h
  have hnew : W'.sent (.publishRequest n s (W.node n).lastAcceptedTerm (W.node n).lastAcceptedVersion) := by
    rw [← hW']; exact Or.inr rfl
  have hpr : ∀ a s' pt' pv', W'.sent (.publishRequest a s' pt' pv') → W.sent (.publishRequest a s' pt' pv') ∨
      (a = n ∧ s' = s ∧ pt' = (W.node n).lastAcceptedTerm ∧ pv' = (W.node n).lastAcceptedVersion) := by
    intro a s' pt' pv' h'; rw [← hW'] at h'
    rcases h' with h' | h'
    · exact Or.inl h'
    · cases h'; exact Or.inr ⟨rfl, rfl, rfl, rfl⟩
  have hrs : ∀ a d r, W'.sent (.publishResponse a d r) → W.sent (.publishResponse a d r) := by
    intro _ _ _ h'; rw [← hW'] at h'
    rcases h' with h' | h'
    · exact h'
    · cases h'
  have hjn : ∀ j, W'.sent (.join j) → W.sent (.join j) := by
    intro _ h'; rw [← hW'] at h'
    rcases h' with h' | h'
    · exact h'
    · cases h'
  have hac : ∀ c, W'.sent (.applyCommit c) → W.sent (.applyCommit c) := by
    intro _ h'; rw [← hW'] at h'
    rcases h' with h' | h'
    · exact h'
    · cases h'
  have hnode : ∀ m, m ≠ n → W'.node m = W.node m := fun m hm => by rw [← hW']; exact set_node_ne _ _ _ _ hm
  have hnode_n : W'.node n = cs' := by rw [← hW']; exact set_node_self _ _ _
  have hparent : Parent W' (W.node n).lastAcceptedTerm (W.node n).lastAcceptedVersion s.term s.version :=
    ⟨n, s, hnew, rfl, rfl⟩
  -- the publications of the term so far descend to the accepted key (the leader's previous publication)
  have hold_term : ∀ a s' pt' pv', W.sent (.publishRequest a s' pt' pv') → s'.term = s.term →
      s'.version ≤ (W.node n).lastAcceptedVersion ∧
      Descends W s'.term s'.version (W.node n).lastAcceptedTerm (W.node n).lastAcceptedVersion := by
    intro a s' pt' pv' hs' ht'
    rcases hinv.leader_settled n hew hlpv with ⟨hlt, -⟩ | ⟨-, hnone⟩
    · obtain ⟨h1, h2, -, -⟩ := hinv.leader_pubs n hew a s' pt' pv' hs' (ht'.trans hst)
      rw [hlpv] at h1 h2
      rw [hlt]
      exact ⟨h1, h2⟩
    · exact absurd (ht'.trans hst) (hnone a s' pt' pv' hs')
  -- other leaders are in other terms
  have hother : ∀ m, m ≠ n → (W.node m).electionWon = true → (W.node m).currentTerm ≠ s.term := by
    intro m hm hwm hct
    exact hm (hinv.won_unique m n _ (inv_won_of_electionWon P W hinv m hwm)
      (by rw [hct, hst]; exact inv_won_of_electionWon P W hinv n hew))
  have hwon : ∀ a t, Won P W' a t → Won P W a t := by
    rintro a t ⟨he, hw | ⟨s', pt', pv', hs', hst'⟩⟩
    · by_cases ha : a = n
      · subst ha; rw [hnode_n, e_ew, e_ct] at hw; exact ⟨he, Or.inl hw⟩
      · rw [hnode a ha] at hw; exact ⟨he, Or.inl hw⟩
    · rcases hpr _ _ _ _ hs' with hs0 | ⟨rfl, rfl, -, -⟩
      · exact ⟨he, Or.inr ⟨s', pt', pv', hs0, hst'⟩⟩
      · rw [← hst', hst]; exact inv_won_of_electionWon P W hinv a hew
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
    · subst hm; rw [hnode_n, e_ew, hew]; intro h'; cases h'
    · rw [hnode m hm]; exact hinv.idle_of_not_won m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew, e_sj]; exact hinv.won_started m
    · rw [hnode m hm]; exact hinv.won_started m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_jv, e_sj]; exact hinv.votes_started m
    · rw [hnode m hm]; exact hinv.votes_started m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_sj, e_ct]; exact hinv.started_term_pos m
    · rw [hnode m hm]; exact hinv.started_term_pos m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew, e_jv, e_lcc, e_lac]; exact hinv.won_quorum m
    · rw [hnode m hm]; exact hinv.won_quorum m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew, e_jv, e_lcc, e_lac]; exact hinv.not_won_no_quorum m
    · rw [hnode m hm]; exact hinv.not_won_no_quorum m
  · intro m x
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_jv, e_ct, e_lat, e_lav]
      intro hx
      obtain ⟨he, j, hj, h1⟩ := hinv.joinVotes_sent m x hx
      exact ⟨he, j, hg _ hj, h1⟩
    · rw [hnode m hm]
      intro hx
      obtain ⟨he, j, hj, h1⟩ := hinv.joinVotes_sent m x hx
      exact ⟨he, j, hg _ hj, h1⟩
  · intro m x
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_pv]; intro hx; cases hx
    · rw [hnode m hm]
      intro hx
      obtain ⟨he, h1⟩ := hinv.publishVotes_sent m x hx
      exact ⟨he, hg _ h1⟩
  · intro m hme
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_lat, e_ct]; exact hinv.term_le m hme
    · rw [hnode m hm]; exact hinv.term_le m hme
  · intro m hme
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_lat, e_lav, e_lcc, e_lac]
      exact (hinv.accepted_realizes m hme).imp id (realizes_mono hg)
    · rw [hnode m hm]; exact (hinv.accepted_realizes m hme).imp id (realizes_mono hg)
  · intro j hj; exact hinv.join_wf j (hjn j hj)
  · intro j hj hje
    by_cases hm : j.sourceNode.id = n
    · rw [hm, hnode_n, e_ct]; have := hinv.join_term_le j (hjn j hj) hje; rw [hm] at this; exact this
    · rw [hnode _ hm]; exact hinv.join_term_le j (hjn j hj) hje
  · intro j j' hj hj'; exact hinv.join_unique j j' (hjn j hj) (hjn j' hj')
  · intro j a d r hj hr; exact hinv.join_after_response j a d r (hjn j hj) (hrs a d r hr)
  · intro a d r hr ha
    by_cases hm : a = n
    · subst hm; rw [hnode_n, e_ct, e_lat, e_lav]; exact hinv.response_le a d r (hrs a d r hr) ha
    · rw [hnode a hm]; exact hinv.response_le a d r (hrs a d r hr) ha
  · intro a d r hr
    obtain ⟨s', pt', pv', hs', h1, h2⟩ := hinv.response_published a d r (hrs a d r hr)
    exact ⟨s', pt', pv', hg _ hs', h1, h2⟩
  · intro a s' pt' pv' hs'
    rcases hpr _ _ _ _ hs' with hs0 | ⟨rfl, rfl, rfl, rfl⟩
    · exact hinv.pub_wf _ _ _ _ hs0
    · refine ⟨hne, by omega, by have := hinv.term_le a hne; omega, hsv, ?_⟩
      intro h0
      rcases hreal with ⟨-, hxy, hX⟩ | ⟨src₂, s₂, pt₂, pv₂, hs₂, h1, -⟩
      · rw [hlcc]; exact hX
      · have := (hinv.pub_wf _ _ _ _ hs₂).2.1; omega
  · intro a s' pt' pv' hs' hpt
    rcases hpr _ _ _ _ hs' with hs0 | ⟨rfl, rfl, rfl, rfl⟩
    · obtain ⟨src', s'', pt'', pv'', hs'', h1, h2, h3, h4⟩ := hinv.pub_parent _ _ _ _ hs0 hpt
      exact ⟨src', s'', pt'', pv'', hg _ hs'', h1, h2, h3.imp id (fun h => ⟨h.1, committed_mono hg h.2⟩), h4⟩
    · rcases hreal with ⟨h0, -⟩ | ⟨src₂, s₂, pt₂, pv₂, hs₂, h1, h2, h3, h4⟩
      · omega
      · refine ⟨src₂, s₂, pt₂, pv₂, hg _ hs₂, h1, h2, ?_, ?_⟩
        · rw [hlcc]; exact h4.imp id (fun h => ⟨h.1, committed_mono hg h.2⟩)
        · intro hac'
          rcases hreconf with hr | hr
          · exact absurd (hr.trans h3) hac'
          · rw [hlcc, hr, h3]
  · intro a₁ s₁ pt₁ pv₁ a₂ s₂ pt₂ pv₂ h₁ h₂ ht hv
    rcases hpr _ _ _ _ h₁ with h₁' | ⟨rfl, rfl, rfl, rfl⟩ <;>
      rcases hpr _ _ _ _ h₂ with h₂' | ⟨rfl, rfl, rfl, rfl⟩
    · exact hinv.pub_unique _ _ _ _ _ _ _ _ h₁' h₂' ht hv
    · have := (hold_term _ _ _ _ h₁' ht).1; omega
    · have := (hold_term _ _ _ _ h₂' ht.symm).1; omega
    · exact ⟨rfl, rfl, rfl, rfl⟩
  · intro a s' pt' pv' hs'
    rcases hpr _ _ _ _ hs' with hs0 | ⟨rfl, rfl, rfl, rfl⟩
    · obtain ⟨v₀, h'⟩ := hinv.pub_rooted _ _ _ _ hs0
      exact ⟨v₀, descends_mono hg h'⟩
    · rcases hreal with ⟨h0, -⟩ | ⟨src₂, s₂, pt₂, pv₂, hs₂, h1, h2, -⟩
      · refine ⟨(W.node a).lastAcceptedVersion, .step _ _ _ _ _ _ ?_ hparent⟩
        rw [← h0]; exact .refl _ _
      · obtain ⟨v₀, h'⟩ := hinv.pub_rooted _ _ _ _ hs₂
        rw [h1, h2] at h'
        exact ⟨v₀, .step _ _ _ _ _ _ (descends_mono hg h') hparent⟩
  · intro a₁ s₁ pt₁ pv₁ a₂ s₂ pt₂ pv₂ h₁ h₂ ht
    rcases hpr _ _ _ _ h₁ with h₁' | ⟨rfl, rfl, rfl, rfl⟩ <;>
      rcases hpr _ _ _ _ h₂ with h₂' | ⟨rfl, rfl, rfl, rfl⟩
    · exact (hinv.pub_same_term _ _ _ _ _ _ _ _ h₁' h₂' ht).imp (descends_mono hg) (descends_mono hg)
    · exact Or.inl (.step _ _ _ _ _ _ (descends_mono hg (hold_term _ _ _ _ h₁' ht).2) hparent)
    · exact Or.inr (.step _ _ _ _ _ _ (descends_mono hg (hold_term _ _ _ _ h₂' ht.symm).2) hparent)
    · exact Or.inl (.refl _ _)
  · intro a s' pt' pv' hs'
    rcases hpr _ _ _ _ hs' with hs0 | ⟨rfl, rfl, rfl, rfl⟩
    · obtain ⟨J, h1, h2, h3⟩ := hinv.pub_voters _ _ _ _ hs0
      exact ⟨J, joinVoters_mono hg h1, h2, h3⟩
    · refine ⟨(W.node a).joinVotes.nodes, ?_, by rw [hlcc]; exact hq1, hq⟩
      intro x hx
      obtain ⟨he, j, hj, h1, h2, h3, -⟩ := hinv.joinVotes_sent a x hx
      exact ⟨he, j, hg _ hj, h1, h2, by rw [h3, hst]⟩
  · intro a s' pt' pv' hs' hpt
    rcases hpr _ _ _ _ hs' with hs0 | ⟨rfl, rfl, rfl, rfl⟩
    · obtain ⟨y, J, h1⟩ := hinv.pub_election _ _ _ _ hs0 hpt
      exact ⟨y, J, electionRecord_mono hg h1⟩
    · refine ⟨(W.node a).lastAcceptedConfiguration, (W.node a).joinVotes.nodes, hpt,
        by rw [hlcc]; exact realizes_mono hg hreal, ?_, by rw [hlcc]; exact hq1, hq2⟩
      intro x hx
      obtain ⟨he, j, hj, h1, h2, h3, h4⟩ := hinv.joinVotes_sent a x hx
      exact ⟨he, j, hg _ hj, h1, h2, by rw [h3, hst], h4⟩
  · intro c hc
    obtain ⟨src, s', pt, pv, hs', h1, h2, A, hA, h3, h4⟩ := hinv.commit_quorum c (hac c hc)
    refine ⟨src, s', pt, pv, hg _ hs', h1, h2, A, respVoters_mono hg hA, h3, ?_⟩
    rcases h4 with h4 | ⟨h4, src', s'', pt', pv', hs'', h5, h6, h7⟩
    · exact Or.inl h4
    · exact Or.inr ⟨committed_mono hg h4, src', s'', pt', pv', hg _ hs'', h5, h6, h7⟩
  · intro a b t ha hb
    exact hinv.won_unique a b t (hwon a t ha) (hwon b t hb)
  · intro a s' pt' pv' hs'
    rcases hpr _ _ _ _ hs' with hs0 | ⟨rfl, rfl, rfl, rfl⟩
    · by_cases hm : a = n
      · subst hm; rw [hnode_n, e_ct, e_ew, e_sj]; exact hinv.pub_source_term _ _ _ _ hs0
      · rw [hnode a hm]; exact hinv.pub_source_term _ _ _ _ hs0
    · rw [hnode_n, e_ct, e_ew]; exact Or.inr ⟨hst, Or.inl hew⟩
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew, e_ct, e_lpv, e_jv]
      intro _ a s' pt' pv' hs' ht'
      rcases hpr _ _ _ _ hs' with hs0 | ⟨rfl, rfl, rfl, rfl⟩
      · obtain ⟨h1, h2⟩ := hold_term _ _ _ _ hs0 (ht'.trans hst.symm)
        obtain ⟨-, -, h3, h4⟩ := hinv.leader_pubs m hew _ _ _ _ hs0 ht'
        refine ⟨by omega, ?_, h3, h4⟩
        rw [← hst]
        exact .step _ _ _ _ _ _ (descends_mono hg h2) hparent
      · exact ⟨Int.le_refl _, by rw [← hst]; exact .refl _ _, by rw [hlcc]; exact hq1, hq⟩
    · rw [hnode m hm]
      intro hw a s' pt' pv' hs' ht'
      rcases hpr _ _ _ _ hs' with hs0 | ⟨rfl, rfl, rfl, rfl⟩
      · obtain ⟨h1, h2, h3, h4⟩ := hinv.leader_pubs m hw _ _ _ _ hs0 ht'
        exact ⟨h1, descends_mono hg h2, h3, h4⟩
      · exact absurd ht'.symm (hother m hm hw)
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew, e_lpv, e_lav, e_lat, e_ct, e_lpc, e_lcc]
      intro _ _
      exact ⟨s, hnew, hst, rfl, rfl, Or.inl hlcc.symm⟩
    · rw [hnode m hm]
      intro hw hne'
      obtain ⟨s', hs', h1, h2, h3, h4⟩ := hinv.leader_inflight m hw hne'
      exact ⟨s', hg _ hs', h1, h2, h3, h4.imp id (fun h => ⟨h.1, committed_mono hg h.2.1, h.2.2⟩)⟩
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_lpv, e_lav]
      intro _ hv
      omega
    · rw [hnode m hm]
      intro hw hv
      rcases hinv.leader_settled m hw hv with h' | ⟨h1, h2⟩
      · exact Or.inl h'
      · refine Or.inr ⟨h1, fun a s' pt' pv' hs' => ?_⟩
        rcases hpr _ _ _ _ hs' with hs0 | ⟨rfl, rfl, rfl, rfl⟩
        · exact h2 _ _ _ _ hs0
        · exact fun ht' => hother m hm hw ht'.symm

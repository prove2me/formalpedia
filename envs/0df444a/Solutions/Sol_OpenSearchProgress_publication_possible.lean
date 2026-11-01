-- Prove2me | solution 1 for OpenSearchProgress.publication_possible
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T01:22:48.905202+00:00
-- url     : https://prove2.me/submissions/9723afe6-329f-415f-9c00-b33cfed42961

import Definitions.Def_OpenSearchProgress
import Theorems.Thm_OpenSearchSafety_reachable_inv
import Theorems.Thm_OpenSearchSafety_inv_descends_parent
import Theorems.Thm_OpenSearchSafety_inv_descends_key
import Theorems.Thm_OpenSearchSafety_inv_eligible_of_won
import Theorems.Thm_OpenSearchProgress_publication_committed

open OpenSearchCoordination OpenSearchSafety OpenSearchProgress

private theorem set_node_self {V : Type} (W : Cluster V) (n : NodeId) (cs : CoordinationState V) :
    (W.set n cs).node n = cs := by
  simp [Cluster.set]

private theorem set_node_ne {V : Type} (W : Cluster V) (n m : NodeId) (cs : CoordinationState V) (h : m ≠ n) :
    (W.set n cs).node m = W.node m := by
  simp [Cluster.set, h]

private theorem send_node {V : Type} (W : Cluster V) (m : Message V) : (W.send m).node = W.node := rfl

private theorem estep_step {V : Type} {P : Params} {c : NodeId} {t : Nat} {Q : List NodeId} {kt : Nat} {kv : Int}
    {W W' : Cluster V} (h : ElectionStep P c t Q kt kv W W') : Step P W W' := by
  cases h with
  | bootstrap n X s cs' hX _ hcontract hconf h => exact .bootstrap W n X s cs' hX hcontract hconf h
  | startJoin n src t' cs' j hsrc _ h => exact .startJoin W n src t' cs' j hsrc h
  | join n j cs' b hsent hdest h => exact .join W n j cs' b hsent hdest h
  | publish n src s pt pv cs' r hsent _ h => exact .publish W n src s pt pv cs' r hsent h
  | respond n src r cs' o hsent h => exact .respond W n src r cs' o hsent h
  | commit n a cs' hsent h => exact .commit W n a cs' hsent h
  | restart n s' hn _ hs => exact .restart W n s' hn hs
  | restartAny n t' s' hn => exact .restartAny W n t' s' hn

private theorem pstep_step {V : Type} {P : Params} {c : NodeId} {t : Nat} {Q : List NodeId}
    {W W' : Cluster V} (h : PublicationStep P c t Q W W') : Step P W W' := by
  cases h with
  | bootstrap n X s cs' hX hcontract hconf h => exact .bootstrap W n X s cs' hX hcontract hconf h
  | startJoin n src t' cs' j hsrc _ h => exact .startJoin W n src t' cs' j hsrc h
  | join n j cs' b hsent hdest h => exact .join W n j cs' b hsent hdest h
  | clientValue n s cs' p _ hcontract h => exact .clientValue W n s cs' p hcontract h
  | publish n src s pt pv cs' r hsent h => exact .publish W n src s pt pv cs' r hsent h
  | respond n src r cs' o hsent h => exact .respond W n src r cs' o hsent h
  | commit n a cs' hsent h => exact .commit W n a cs' hsent h
  | restart n s' hn _ hs => exact .restart W n s' hn hs
  | restartAny n t' s' hn => exact .restartAny W n t' s' hn

private theorem step_sent {V : Type} {P : Params} {W W' : Cluster V} (h : Step P W W') :
    ∀ m, W.sent m → W'.sent m := by
  intro m hm
  cases h with
  | bootstrap => exact hm
  | startJoin => exact Or.inl hm
  | join => exact hm
  | clientValue => exact Or.inl hm
  | publish => exact Or.inl hm
  | respond n src r cs' o hsent h =>
    cases o with
    | none => exact hm
    | some a => exact Or.inl hm
  | commit => exact hm
  | restart => exact hm
  | restartAny => exact hm

private theorem eexec_reach {V : Type} {P : Params} {c : NodeId} {t : Nat} {Q : List NodeId} {kt : Nat} {kv : Int}
    {W W' : Cluster V} (hW : Reachable P W) (h : ElectionExec P c t Q kt kv W W') : Reachable P W' := by
  induction h with
  | refl => exact hW
  | step W₁ W₂ _ hs ih => exact .step _ _ ih (estep_step hs)

private theorem pexec_reach {V : Type} {P : Params} {c : NodeId} {t : Nat} {Q : List NodeId}
    {W W' : Cluster V} (hW : Reachable P W) (h : PublicationExec P c t Q W W') : Reachable P W' := by
  induction h with
  | refl => exact hW
  | step W₁ W₂ _ hs ih => exact .step _ _ ih (pstep_step hs)

private theorem pexec_sent {V : Type} {P : Params} {c : NodeId} {t : Nat} {Q : List NodeId}
    {W W' : Cluster V} (h : PublicationExec P c t Q W W') : ∀ m, W.sent m → W'.sent m := by
  induction h with
  | refl => exact fun _ h => h
  | step W₁ W₂ _ hs ih => exact fun m hm => step_sent (pstep_step hs) m (ih m hm)

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

/-- A quorum is a nonempty list. -/
private theorem ne_nil_of_hasQuorum (c : VotingConfiguration) (a : List NodeId) (h : c.hasQuorum a = true) :
    a ≠ [] := by
  intro e
  rw [e, hasQuorum_nil] at h
  cases h

/-- A configuration with no node has no quorum. -/
private theorem hasQuorum_of_isEmpty (c : VotingConfiguration) (a : List NodeId) (h : c.isEmpty = true) :
    c.hasQuorum a = false := by
  unfold VotingConfiguration.isEmpty at h
  rw [List.isEmpty_iff] at h
  unfold VotingConfiguration.hasQuorum
  rw [h]
  simp

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

private theorem markCommitted_mv {V : Type} (s : ClusterState V) :
    s.markCommitted.metadataVersion = s.metadataVersion := by
  unfold ClusterState.markCommitted
  dsimp only
  split <;> split <;> simp_all

private theorem vomv_pos {V : Type} (s : ClusterState V) (h : s.term ≠ 0) :
    s.versionOrMetadataVersion = s.version := by
  unfold ClusterState.versionOrMetadataVersion
  split
  · rename_i hc; exact absurd hc h
  · rfl

private theorem markCommitted_vomv {V : Type} (s : ClusterState V) :
    s.markCommitted.versionOrMetadataVersion = s.versionOrMetadataVersion := by
  obtain ⟨mt, mv, -, -⟩ := markCommitted_spec s
  unfold ClusterState.versionOrMetadataVersion
  rw [mt, mv, markCommitted_mv]

private theorem startJoin_ok {V : Type} (cs : CoordinationState V) (req : StartJoinRequest)
    (h : cs.currentTerm < req.term) : ∃ cs' j, cs.handleStartJoin req = .ok (cs', j) := by
  unfold CoordinationState.handleStartJoin
  rw [if_neg (by omega)]
  exact ⟨_, _, rfl⟩

private theorem join_ok {V : Type} (es : ElectionStrategy) (cs : CoordinationState V) (j : Join)
    (h1 : j.term = cs.currentTerm) (h2 : cs.startedJoinSinceLastReboot = true)
    (h3 : j.lastAcceptedTerm < cs.lastAcceptedTerm ∨
      (j.lastAcceptedTerm = cs.lastAcceptedTerm ∧ j.lastAcceptedVersion ≤ cs.lastAcceptedVersionOrMetadataVersion))
    (h4 : cs.lastAcceptedConfiguration.isEmpty = false) :
    ∃ cs' b, cs.handleJoin es j = .ok (cs', b) := by
  unfold CoordinationState.handleJoin
  rw [if_neg (by omega), if_neg (by simp [h2]), if_neg (by omega), if_neg (by omega), if_neg (by simp [h4])]
  exact ⟨_, _, rfl⟩

private theorem publish_ok {V : Type} (cs : CoordinationState V) (s : ClusterState V)
    (h1 : s.term = cs.currentTerm) (h2 : ¬ (s.term = cs.lastAcceptedTerm ∧ s.version ≤ cs.lastAcceptedVersion)) :
    ∃ cs' r, cs.handlePublishRequest ⟨s⟩ = .ok (cs', r) := by
  unfold CoordinationState.handlePublishRequest
  dsimp only
  rw [if_neg (by omega), if_neg h2]
  exact ⟨_, _, rfl⟩

private theorem respond_ok {V : Type} (cs : CoordinationState V) (src : DiscoveryNode) (r : PublishResponse)
    (h1 : cs.electionWon = true) (h2 : r.term = cs.currentTerm) (h3 : r.version = cs.lastPublishedVersion) :
    ∃ cs' o, cs.handlePublishResponse src r = .ok (cs', o) ∧
      (cs.isPublishQuorum (cs.publishVotes.addVote src).1 = true → o = some ⟨cs.localNode, r.term, r.version⟩) := by
  unfold CoordinationState.handlePublishResponse
  rw [if_neg (by simp [h1]), if_neg (by omega), if_neg (by omega)]
  dsimp only
  split
  · exact ⟨_, _, rfl, fun _ => rfl⟩
  · rename_i hq
    refine ⟨_, _, rfl, fun h => absurd ?_ hq⟩
    unfold CoordinationState.isPublishQuorum at h ⊢
    exact h

/-- `handlePublishResponse` sends the commit when the votes, with the new one, are a publish quorum. -/
private theorem respond_quorum {V : Type} (cs : CoordinationState V) (src : DiscoveryNode) (r : PublishResponse)
    (cs' : CoordinationState V) (o : Option ApplyCommitRequest) (h : cs.handlePublishResponse src r = .ok (cs', o))
    (hq : cs.isPublishQuorum (cs.publishVotes.addVote src).1 = true) :
    o = some ⟨cs.localNode, r.term, r.version⟩ := by
  unfold CoordinationState.handlePublishResponse at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  dsimp only at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  · rename_i hn
    exact absurd hq hn

/-- In a cluster satisfying `Inv`, every node's `localNode` carries the node's id. -/
private theorem localNode_id {V : Type} {P : Params} {W : Cluster V} (hinv : Inv P W) (n : NodeId) :
    (W.node n).localNode.id = n := by
  rw [hinv.localNode_eq n]; rfl

/-- An eligible node whose accepted state has a term ≥ 1 has sent a publish response for its accepted (term,
version): only `handlePublishRequest` installs such a state, and it sends the response; commits and restarts keep
the term and the version. -/
private theorem reach_responded {V : Type} (P : Params) (W : Cluster V) (hW : Reachable P W) :
    ∀ n, P.eligible n = true → 1 ≤ (W.node n).lastAcceptedTerm →
      ∃ d, W.sent (.publishResponse n d ⟨(W.node n).lastAcceptedTerm, (W.node n).lastAcceptedVersion⟩) := by
  induction hW with
  | init W h =>
    intro n _ hpos
    obtain ⟨s, hs0, -, -, he⟩ := h.1 n
    rw [he] at hpos
    exact absurd hpos (by show ¬ 1 ≤ s.term; omega)
  | step W W' _ hs ih =>
    intro n hn hpos
    cases hs with
    | bootstrap m X s cs' hX hcontract hconf h =>
      obtain ⟨-, rfl⟩ := spec_setInitialState _ _ _ h
      by_cases hm : n = m
      · subst hm
        rw [set_node_self] at hpos
        exact absurd hpos (by show ¬ 1 ≤ s.term; have := hcontract.2.2.2.2.2.2.2.1; omega)
      · rw [set_node_ne _ _ _ _ hm] at hpos ⊢
        exact ih n hn hpos
    | startJoin m src t cs' j hsrc h =>
      obtain ⟨-, rfl, rfl⟩ := spec_startJoin _ _ _ _ h
      rw [send_node] at hpos ⊢
      by_cases hm : n = m
      · subst hm
        rw [set_node_self] at hpos ⊢
        obtain ⟨d, hd⟩ := ih n hn hpos
        exact ⟨d, Or.inl hd⟩
      · rw [set_node_ne _ _ _ _ hm] at hpos ⊢
        obtain ⟨d, hd⟩ := ih n hn hpos
        exact ⟨d, Or.inl hd⟩
    | join m j cs' b hsent hdest h =>
      obtain ⟨-, -, -, -, rfl⟩ := spec_join _ _ _ _ _ h
      by_cases hm : n = m
      · subst hm
        rw [set_node_self] at hpos ⊢
        exact ih n hn hpos
      · rw [set_node_ne _ _ _ _ hm] at hpos ⊢
        exact ih n hn hpos
    | clientValue m s cs' p hcontract h =>
      obtain ⟨-, -, -, -, -, -, -, rfl⟩ := spec_clientValue _ _ _ _ h
      rw [send_node] at hpos ⊢
      by_cases hm : n = m
      · subst hm
        rw [set_node_self] at hpos ⊢
        obtain ⟨d, hd⟩ := ih n hn hpos
        exact ⟨d, Or.inl hd⟩
      · rw [set_node_ne _ _ _ _ hm] at hpos ⊢
        obtain ⟨d, hd⟩ := ih n hn hpos
        exact ⟨d, Or.inl hd⟩
    | publish m src s pt pv cs' r hsent h =>
      obtain ⟨-, -, rfl, rfl⟩ := spec_publish _ _ _ _ h
      rw [send_node] at hpos ⊢
      by_cases hm : n = m
      · subst hm
        rw [set_node_self] at hpos ⊢
        exact ⟨src, Or.inr rfl⟩
      · rw [set_node_ne _ _ _ _ hm] at hpos ⊢
        obtain ⟨d, hd⟩ := ih n hn hpos
        exact ⟨d, Or.inl hd⟩
    | respond m src r cs' o hsent h =>
      obtain ⟨-, -, -, rfl, -⟩ := spec_respond _ _ _ _ _ h
      cases o with
      | none =>
        dsimp only at hpos ⊢
        by_cases hm : n = m
        · subst hm
          rw [set_node_self] at hpos ⊢
          exact ih n hn hpos
        · rw [set_node_ne _ _ _ _ hm] at hpos ⊢
          exact ih n hn hpos
      | some a =>
        dsimp only at hpos ⊢
        rw [send_node] at hpos ⊢
        by_cases hm : n = m
        · subst hm
          rw [set_node_self] at hpos ⊢
          obtain ⟨d, hd⟩ := ih n hn hpos
          exact ⟨d, Or.inl hd⟩
        · rw [set_node_ne _ _ _ _ hm] at hpos ⊢
          obtain ⟨d, hd⟩ := ih n hn hpos
          exact ⟨d, Or.inl hd⟩
    | commit m a cs' hsent h =>
      obtain ⟨-, -, -, rfl⟩ := spec_commit _ _ _ h
      obtain ⟨mt, mv, -, -⟩ := markCommitted_spec (W.node m).lastAcceptedState
      by_cases hm : n = m
      · subst hm
        rw [set_node_self] at hpos ⊢
        have e1 : ({ W.node n with lastAcceptedState := (W.node n).lastAcceptedState.markCommitted } :
            CoordinationState _).lastAcceptedTerm = (W.node n).lastAcceptedTerm := mt
        have e2 : ({ W.node n with lastAcceptedState := (W.node n).lastAcceptedState.markCommitted } :
            CoordinationState _).lastAcceptedVersion = (W.node n).lastAcceptedVersion := mv
        rw [e1] at hpos
        rw [e1, e2]
        exact ih n hn hpos
      · rw [set_node_ne _ _ _ _ hm] at hpos ⊢
        exact ih n hn hpos
    | restart m s' hm' hs =>
      by_cases hm : n = m
      · subst hm
        rw [set_node_self] at hpos ⊢
        rcases hs with ⟨h1, h2, -⟩ | ⟨-, -, -, -, h0, -⟩
        · have e1 : (CoordinationState.init (W.node n).localNode (W.node n).currentTerm s').lastAcceptedTerm =
              (W.node n).lastAcceptedTerm := h1
          have e2 : (CoordinationState.init (W.node n).localNode (W.node n).currentTerm s').lastAcceptedVersion =
              (W.node n).lastAcceptedVersion := h2
          rw [e1] at hpos
          rw [e1, e2]
          exact ih n hn hpos
        · exact absurd hpos (by show ¬ 1 ≤ s'.term; omega)
      · rw [set_node_ne _ _ _ _ hm] at hpos ⊢
        exact ih n hn hpos
    | restartAny m t s' hm' =>
      by_cases hm : n = m
      · subst hm; rw [hm'] at hn; cases hn
      · rw [set_node_ne _ _ _ _ hm] at hpos ⊢
        exact ih n hn hpos

/-- During a stable election, the candidate's accepted state keeps its term, version, metadata version and last
accepted configuration (a publication at most as fresh as its own accepted state is rejected; a commit only copies
the last accepted configuration into the last committed one), and once it has left its initial term it has started
a join. -/
private theorem elect_c {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat) (Q : List NodeId) (hc : P.eligible c = true) (hct : (W.node c).currentTerm < t)
    (W' : Cluster V) (hE : ElectionExec P c t Q (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion W W') :
    (W'.node c).lastAcceptedTerm = (W.node c).lastAcceptedTerm ∧
    (W'.node c).lastAcceptedVersion = (W.node c).lastAcceptedVersion ∧
    (W'.node c).lastAcceptedState.metadataVersion = (W.node c).lastAcceptedState.metadataVersion ∧
    (W'.node c).lastAcceptedConfiguration = (W.node c).lastAcceptedConfiguration ∧
    ((W'.node c).lastCommittedConfiguration = (W.node c).lastCommittedConfiguration ∨
      (W'.node c).lastCommittedConfiguration = (W.node c).lastAcceptedConfiguration) ∧
    ((W'.node c).currentTerm < t ∨ (W'.node c).startedJoinSinceLastReboot = true) := by
  induction hE with
  | refl => exact ⟨rfl, rfl, rfl, rfl, Or.inl rfl, Or.inl hct⟩
  | step X X' hEX hs ih =>
    have hinv := reachable_inv P hP hes X (eexec_reach hW hEX)
    obtain ⟨e_t, e_v, e_mv, e_lac, e_lcc, e_sj⟩ := ih
    cases hs with
    | bootstrap n X0 s cs' hX hnq hcontract hconf h =>
      rw [set_node_ne _ _ _ _ (fun e => hnq.1 e.symm)]
      exact ⟨e_t, e_v, e_mv, e_lac, e_lcc, e_sj⟩
    | startJoin n src t' cs' j hsrc hstable h =>
      obtain ⟨-, rfl, rfl⟩ := spec_startJoin _ _ _ _ h
      rw [send_node]
      by_cases hn : c = n
      · subst hn; rw [set_node_self]
        exact ⟨e_t, e_v, e_mv, e_lac, e_lcc, Or.inr rfl⟩
      · rw [set_node_ne _ _ _ _ hn]
        exact ⟨e_t, e_v, e_mv, e_lac, e_lcc, e_sj⟩
    | join n j cs' b hsent hdest h =>
      obtain ⟨-, -, -, -, rfl⟩ := spec_join _ _ _ _ _ h
      by_cases hn : c = n
      · subst hn; rw [set_node_self]
        exact ⟨e_t, e_v, e_mv, e_lac, e_lcc, e_sj⟩
      · rw [set_node_ne _ _ _ _ hn]
        exact ⟨e_t, e_v, e_mv, e_lac, e_lcc, e_sj⟩
    | publish n src s pt pv cs' r hsent hfr h =>
      obtain ⟨hst, hz, rfl, rfl⟩ := spec_publish _ _ _ _ h
      rw [send_node]
      by_cases hn : c = n
      · exfalso
        subst hn
        have hle := hinv.term_le _ hc
        have hpos := (hinv.pub_wf _ _ _ _ hsent).2.1
        dsimp only at hst hz
        rcases hfr (Or.inl rfl) with h1 | ⟨h1, h2⟩
        · omega
        · rcases hz with hz | hz
          · omega
          · exact hz ⟨by omega, by omega⟩
      · rw [set_node_ne _ _ _ _ hn]
        exact ⟨e_t, e_v, e_mv, e_lac, e_lcc, e_sj⟩
    | respond n src r cs' o hsent h =>
      obtain ⟨-, -, -, rfl, -⟩ := spec_respond _ _ _ _ _ h
      cases o with
      | none =>
        dsimp only
        by_cases hn : c = n
        · subst hn; rw [set_node_self]
          exact ⟨e_t, e_v, e_mv, e_lac, e_lcc, e_sj⟩
        · rw [set_node_ne _ _ _ _ hn]
          exact ⟨e_t, e_v, e_mv, e_lac, e_lcc, e_sj⟩
      | some a =>
        dsimp only
        rw [send_node]
        by_cases hn : c = n
        · subst hn; rw [set_node_self]
          exact ⟨e_t, e_v, e_mv, e_lac, e_lcc, e_sj⟩
        · rw [set_node_ne _ _ _ _ hn]
          exact ⟨e_t, e_v, e_mv, e_lac, e_lcc, e_sj⟩
    | commit n a cs' hsent h =>
      obtain ⟨-, -, -, rfl⟩ := spec_commit _ _ _ h
      by_cases hn : c = n
      · subst hn; rw [set_node_self]
        obtain ⟨mt, mv, mlac, mlcc⟩ := markCommitted_spec (X.node c).lastAcceptedState
        exact ⟨mt.trans e_t, mv.trans e_v, (markCommitted_mv _).trans e_mv, mlac.trans e_lac,
          Or.inr (mlcc.trans e_lac), e_sj⟩
      · rw [set_node_ne _ _ _ _ hn]
        exact ⟨e_t, e_v, e_mv, e_lac, e_lcc, e_sj⟩
    | restart n s' hn' hnq hs =>
      rw [set_node_ne _ _ _ _ (fun e => hnq.1 e.symm)]
      exact ⟨e_t, e_v, e_mv, e_lac, e_lcc, e_sj⟩
    | restartAny n t' s' hn' =>
      have hn : c ≠ n := fun e => by rw [e, hn'] at hc; cases hc
      rw [set_node_ne _ _ _ _ hn]
      exact ⟨e_t, e_v, e_mv, e_lac, e_lcc, e_sj⟩

/-- During a stable election, every voter's accepted (term, version) stays at most the candidate's initial one, in
the way `handleJoin` compares them (a voter accepts only publications at most as fresh, and these have terms ≥ 1), and
so does every join for term `t` from a voter to the candidate (it was sent during the election: before it, the voter
was in a lower term). -/
private theorem elect_q {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat) (Q : List NodeId) (hQ : ∀ q ∈ Q, P.eligible q = true)
    (hterm : ∀ q ∈ Q, (W.node q).currentTerm < t)
    (hfresh : ∀ q ∈ Q, (W.node q).lastAcceptedTerm < (W.node c).lastAcceptedTerm ∨
      ((W.node q).lastAcceptedTerm = (W.node c).lastAcceptedTerm ∧
        (W.node q).lastAcceptedVersionOrMetadataVersion ≤ (W.node c).lastAcceptedVersionOrMetadataVersion))
    (W' : Cluster V) (hE : ElectionExec P c t Q (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion W W') :
    (∀ q ∈ Q, (W'.node q).lastAcceptedTerm < (W.node c).lastAcceptedTerm ∨
      ((W'.node q).lastAcceptedTerm = (W.node c).lastAcceptedTerm ∧
        (W'.node q).lastAcceptedVersionOrMetadataVersion ≤ (W.node c).lastAcceptedVersionOrMetadataVersion)) ∧
    (∀ j : Join, W'.sent (.join j) → j.sourceNode.id ∈ Q → j.targetNode.id = c → j.term = t →
      j.lastAcceptedTerm < (W.node c).lastAcceptedTerm ∨
      (j.lastAcceptedTerm = (W.node c).lastAcceptedTerm ∧
        j.lastAcceptedVersion ≤ (W.node c).lastAcceptedVersionOrMetadataVersion)) := by
  induction hE with
  | refl =>
    refine ⟨hfresh, ?_⟩
    intro j hj hsrc _ hjt
    have hinv := reachable_inv P hP hes W hW
    have h1 := hinv.join_term_le j hj (hQ _ hsrc)
    have h2 := hterm _ hsrc
    omega
  | step X X' hEX hs ih =>
    have hinv := reachable_inv P hP hes X (eexec_reach hW hEX)
    obtain ⟨hqk, hjk⟩ := ih
    cases hs with
    | bootstrap n X0 s cs' hX hnq hcontract hconf h =>
      refine ⟨?_, hjk⟩
      intro q hq
      have hqn : q ≠ n := fun e => hnq.2 (e ▸ hq)
      rw [set_node_ne _ _ _ _ hqn]
      exact hqk q hq
    | startJoin n src t' cs' j hsrc hstable h =>
      obtain ⟨-, rfl, rfl⟩ := spec_startJoin _ _ _ _ h
      refine ⟨?_, ?_⟩
      · intro q hq
        rw [send_node]
        by_cases hqn : q = n
        · subst hqn; rw [set_node_self]; exact hqk _ hq
        · rw [set_node_ne _ _ _ _ hqn]; exact hqk q hq
      · intro j' hj' hsrc' htgt' hjt'
        rcases hj' with hj' | hj'
        · exact hjk j' hj' hsrc' htgt' hjt'
        · cases hj'
          have hsn : (X.node n).localNode.id = n := by rw [hinv.localNode_eq n]; rfl
          have hnQ : n ∈ Q := by rw [← hsn]; exact hsrc'
          exact hqk n hnQ
    | join n j cs' b hsent hdest h =>
      obtain ⟨-, -, -, -, rfl⟩ := spec_join _ _ _ _ _ h
      refine ⟨?_, hjk⟩
      intro q hq
      by_cases hqn : q = n
      · subst hqn; rw [set_node_self]; exact hqk _ hq
      · rw [set_node_ne _ _ _ _ hqn]; exact hqk q hq
    | publish n src s pt pv cs' r hsent hfr h =>
      obtain ⟨-, -, rfl, rfl⟩ := spec_publish _ _ _ _ h
      refine ⟨?_, ?_⟩
      · intro q hq
        rw [send_node]
        by_cases hqn : q = n
        · subst hqn; rw [set_node_self]
          have hpos := (hinv.pub_wf _ _ _ _ hsent).2.1
          rcases hfr (Or.inr hq) with h1 | ⟨h1, h2⟩
          · exact Or.inl h1
          · refine Or.inr ⟨h1, ?_⟩
            show s.versionOrMetadataVersion ≤ (W.node c).lastAcceptedState.versionOrMetadataVersion
            rw [vomv_pos s (by omega), vomv_pos _ (by show (W.node c).lastAcceptedTerm ≠ 0; omega)]
            exact h2
        · rw [set_node_ne _ _ _ _ hqn]; exact hqk q hq
      · intro j' hj' hsrc' htgt' hjt'
        rcases hj' with hj' | hj'
        · exact hjk j' hj' hsrc' htgt' hjt'
        · cases hj'
    | respond n src r cs' o hsent h =>
      obtain ⟨-, -, -, rfl, -⟩ := spec_respond _ _ _ _ _ h
      cases o with
      | none =>
        dsimp only
        refine ⟨?_, hjk⟩
        intro q hq
        by_cases hqn : q = n
        · subst hqn; rw [set_node_self]; exact hqk _ hq
        · rw [set_node_ne _ _ _ _ hqn]; exact hqk q hq
      | some a =>
        dsimp only
        refine ⟨?_, ?_⟩
        · intro q hq
          rw [send_node]
          by_cases hqn : q = n
          · subst hqn; rw [set_node_self]; exact hqk _ hq
          · rw [set_node_ne _ _ _ _ hqn]; exact hqk q hq
        · intro j' hj' hsrc' htgt' hjt'
          rcases hj' with hj' | hj'
          · exact hjk j' hj' hsrc' htgt' hjt'
          · cases hj'
    | commit n a cs' hsent h =>
      obtain ⟨-, -, -, rfl⟩ := spec_commit _ _ _ h
      refine ⟨?_, hjk⟩
      intro q hq
      by_cases hqn : q = n
      · subst hqn; rw [set_node_self]
        obtain ⟨mt, -, -, -⟩ := markCommitted_spec (X.node q).lastAcceptedState
        have e1 : ({ X.node q with lastAcceptedState := (X.node q).lastAcceptedState.markCommitted } :
            CoordinationState _).lastAcceptedTerm = (X.node q).lastAcceptedTerm := mt
        have e2 : ({ X.node q with lastAcceptedState := (X.node q).lastAcceptedState.markCommitted } :
            CoordinationState _).lastAcceptedVersionOrMetadataVersion =
            (X.node q).lastAcceptedVersionOrMetadataVersion := markCommitted_vomv _
        rw [e1, e2]; exact hqk _ hq
      · rw [set_node_ne _ _ _ _ hqn]; exact hqk q hq
    | restart n s' hn' hnq hs =>
      refine ⟨?_, hjk⟩
      intro q hq
      have hqn : q ≠ n := fun e => hnq.2 (e ▸ hq)
      rw [set_node_ne _ _ _ _ hqn]
      exact hqk q hq
    | restartAny n t' s' hn' =>
      refine ⟨?_, hjk⟩
      intro q hq
      have hqn : q ≠ n := fun e => by have := hQ q hq; rw [e, hn'] at this; cases this
      rw [set_node_ne _ _ _ _ hqn]
      exact hqk q hq

/-- Votes keep counting: once `c` is in term `t`, every join for `t` from a voter is accepted and counted (its
checks pass by `elect_c` and `elect_q`, and the voter is eligible). -/
private theorem vote_core {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat) (Q : List NodeId) (hc : P.eligible c = true) (hQ : ∀ q ∈ Q, P.eligible q = true)
    (hterm : ∀ q, q = c ∨ q ∈ Q → (W.node q).currentTerm < t)
    (hfresh : ∀ q ∈ Q, (W.node q).lastAcceptedTerm < (W.node c).lastAcceptedTerm ∨
      ((W.node q).lastAcceptedTerm = (W.node c).lastAcceptedTerm ∧
        (W.node q).lastAcceptedVersionOrMetadataVersion ≤ (W.node c).lastAcceptedVersionOrMetadataVersion))
    (hconf : (W.node c).lastAcceptedConfiguration.isEmpty = false)
    (W' : Cluster V)
    (hE : ElectionExec P c t Q (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion W W')
    (hct : (W'.node c).currentTerm = t) (j : Join) (hj : W'.sent (.join j)) (hsrc : j.sourceNode.id ∈ Q)
    (htgt : j.targetNode.id = c) (hjt : j.term = t) :
    ∃ cs' b, (W'.node c).handleJoin P.strategy j = .ok (cs', b) ∧ j.sourceNode.id ∈ cs'.joinVotes.nodes := by
  have hinv := reachable_inv P hP hes W' (eexec_reach hW hE)
  obtain ⟨e_t, e_v, e_mv, e_lac, -, e_sj⟩ := elect_c P hP hes W hW c t Q hc (hterm c (Or.inl rfl)) W' hE
  obtain ⟨-, hjk⟩ := elect_q P hP hes W hW c t Q hQ (fun q hq => hterm q (Or.inr hq)) hfresh W' hE
  have hsj : (W'.node c).startedJoinSinceLastReboot = true := e_sj.resolve_left (by omega)
  have e_vomv : (W'.node c).lastAcceptedVersionOrMetadataVersion =
      (W.node c).lastAcceptedVersionOrMetadataVersion := by
    have e_t' : (W'.node c).lastAcceptedState.term = (W.node c).lastAcceptedState.term := e_t
    have e_v' : (W'.node c).lastAcceptedState.version = (W.node c).lastAcceptedState.version := e_v
    show (W'.node c).lastAcceptedState.versionOrMetadataVersion =
      (W.node c).lastAcceptedState.versionOrMetadataVersion
    unfold ClusterState.versionOrMetadataVersion
    rw [e_t', e_v', e_mv]
  obtain ⟨cs', b, hok⟩ := join_ok P.strategy (W'.node c) j (by omega) hsj
    (by rw [e_t, e_vomv]; exact hjk j hj hsrc htgt hjt) (by rw [e_lac]; exact hconf)
  refine ⟨cs', b, hok, ?_⟩
  obtain ⟨-, -, -, -, hcs⟩ := spec_join _ _ _ _ _ hok
  rw [hcs]
  show j.sourceNode.id ∈ ((W'.node c).joinVotes.addVote j.sourceNode).1.nodes
  rw [addVote_mem]
  refine Or.inr ⟨rfl, ?_⟩
  rw [(hinv.join_wf j hj).1]
  exact hQ _ hsrc

/-- The election is won once the votes are in: a node that has not won holds no quorum of both of its configurations
(`Inv.not_won_no_quorum`), while `Q` is a quorum of both of `c`'s, which have not changed but for a commit
(`elect_c`). -/
private theorem won_core {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat) (Q : List NodeId) (hc : P.eligible c = true) (_hQ : ∀ q ∈ Q, P.eligible q = true)
    (hquorum : (W.node c).lastCommittedConfiguration.hasQuorum Q = true ∧
      (W.node c).lastAcceptedConfiguration.hasQuorum Q = true)
    (hct0 : (W.node c).currentTerm < t)
    (W' : Cluster V)
    (hE : ElectionExec P c t Q (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion W W')
    (_hct : (W'.node c).currentTerm = t) (hvotes : ∀ q ∈ Q, q ∈ (W'.node c).joinVotes.nodes) :
    (W'.node c).electionWon = true := by
  have hinv := reachable_inv P hP hes W' (eexec_reach hW hE)
  obtain ⟨-, -, -, e_lac, e_lcc, -⟩ := elect_c P hP hes W hW c t Q hc hct0 W' hE
  cases hw : (W'.node c).electionWon
  · exfalso
    apply hinv.not_won_no_quorum c hw
    have hsub : ∀ x, x ∈ Q → x ∈ (W'.node c).joinVotes.nodes := hvotes
    unfold VoteCollection.isQuorum
    refine ⟨?_, ?_⟩
    · rcases e_lcc with e | e <;> rw [e]
      · exact quorum_mono _ _ _ hsub hquorum.1
      · exact quorum_mono _ _ _ hsub hquorum.2
    · rw [e_lac]; exact quorum_mono _ _ _ hsub hquorum.2
  · rfl

/-- The start-join phase of a stable election: every voter not yet in term `t` accepts `c`'s start-join request
for `t`; afterwards every voter has sent `c` a join for `t`. -/
private theorem elect_sj_phase {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat) (Q : List NodeId) (hc : P.eligible c = true) :
    ∀ (L : List NodeId) (X : Cluster V),
      ElectionExec P c t Q (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion W X →
      (∀ q ∈ L, q ∈ Q) → (X.node c).currentTerm = t →
      (∀ q, q = c ∨ q ∈ Q → (X.node q).currentTerm < t ∨
        ∃ j : Join, X.sent (.join j) ∧ j.sourceNode.id = q ∧ j.targetNode.id = c ∧ j.term = t) →
      ∃ X', ElectionExec P c t Q (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion W X' ∧
        (X'.node c).currentTerm = t ∧
        (∀ q, q = c ∨ q ∈ Q → (X'.node q).currentTerm < t ∨
          ∃ j : Join, X'.sent (.join j) ∧ j.sourceNode.id = q ∧ j.targetNode.id = c ∧ j.term = t) ∧
        ∀ q ∈ L, ∃ j : Join, X'.sent (.join j) ∧ j.sourceNode.id = q ∧ j.targetNode.id = c ∧ j.term = t := by
  intro L
  induction L with
  | nil => intro X hX _ hct hI; exact ⟨X, hX, hct, hI, fun q hq => by cases hq⟩
  | cons q L ih =>
    intro X hX hL hct hI
    obtain ⟨X1, hX1, hct1, hI1, hL1⟩ :=
      ih X hX (fun x hx => hL x (List.mem_cons.mpr (Or.inr hx))) hct hI
    have hqQ : q ∈ Q := hL q (List.mem_cons.mpr (Or.inl rfl))
    by_cases hlt : (X1.node q).currentTerm < t
    · have hinv := reachable_inv P hP hes X1 (eexec_reach hW hX1)
      obtain ⟨cs', j, h⟩ := startJoin_ok (X1.node q) ⟨P.dn c, t⟩ hlt
      have hqc : q ≠ c := fun e => by rw [e, hct1] at hlt; omega
      obtain ⟨-, hcs, hj⟩ := spec_startJoin _ _ _ _ h
      have hjq : j.sourceNode.id = q ∧ j.targetNode.id = c ∧ j.term = t := by
        rw [hj]; exact ⟨localNode_id hinv q, rfl, rfl⟩
      refine ⟨(X1.set q cs').send (.join j),
        .step _ _ _ hX1 (.startJoin X1 q c t cs' j hc (Or.inr ⟨rfl, rfl⟩) h), ?_, ?_, ?_⟩
      · rw [send_node, set_node_ne _ _ _ _ (Ne.symm hqc)]; exact hct1
      · intro x hx
        by_cases hxq : x = q
        · subst hxq; exact Or.inr ⟨j, Or.inr rfl, hjq⟩
        · rw [send_node, set_node_ne _ _ _ _ hxq]
          rcases hI1 x hx with h1 | ⟨j', hj', h2⟩
          · exact Or.inl h1
          · exact Or.inr ⟨j', Or.inl hj', h2⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨j, Or.inr rfl, hjq⟩
        · obtain ⟨j', hj', h2⟩ := hL1 x hx; exact ⟨j', Or.inl hj', h2⟩
    · refine ⟨X1, hX1, hct1, hI1, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rcases hI1 x (Or.inr hqQ) with h1 | h1
        · exact absurd h1 hlt
        · exact h1
      · exact hL1 x hx

/-- The join phase of a stable election: `c` handles the join of every voter, and counts it. -/
private theorem elect_join_phase {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat) (Q : List NodeId) (hc : P.eligible c = true) (hQ : ∀ q ∈ Q, P.eligible q = true)
    (hterm : ∀ q, q = c ∨ q ∈ Q → (W.node q).currentTerm < t)
    (hfresh : ∀ q ∈ Q, (W.node q).lastAcceptedTerm < (W.node c).lastAcceptedTerm ∨
      ((W.node q).lastAcceptedTerm = (W.node c).lastAcceptedTerm ∧
        (W.node q).lastAcceptedVersionOrMetadataVersion ≤ (W.node c).lastAcceptedVersionOrMetadataVersion))
    (hconf : (W.node c).lastAcceptedConfiguration.isEmpty = false) :
    ∀ (L : List NodeId) (X : Cluster V),
      ElectionExec P c t Q (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion W X →
      (∀ q ∈ L, q ∈ Q) → (X.node c).currentTerm = t →
      (∀ q ∈ L, ∃ j : Join, X.sent (.join j) ∧ j.sourceNode.id = q ∧ j.targetNode.id = c ∧ j.term = t) →
      ∃ X', ElectionExec P c t Q (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion W X' ∧
        (X'.node c).currentTerm = t ∧ (∀ m, X.sent m → X'.sent m) ∧
        (∀ x, x ∈ (X.node c).joinVotes.nodes → x ∈ (X'.node c).joinVotes.nodes) ∧
        ∀ q ∈ L, q ∈ (X'.node c).joinVotes.nodes := by
  intro L
  induction L with
  | nil => intro X hX _ hct _; exact ⟨X, hX, hct, fun _ h => h, fun _ h => h, fun q hq => by cases hq⟩
  | cons q L ih =>
    intro X hX hL hct hJ
    obtain ⟨X1, hX1, hct1, hg1, hv1, hL1⟩ := ih X hX (fun x hx => hL x (List.mem_cons.mpr (Or.inr hx))) hct
      (fun x hx => hJ x (List.mem_cons.mpr (Or.inr hx)))
    obtain ⟨j, hj, hjs, hjt, hjterm⟩ := hJ q (List.mem_cons.mpr (Or.inl rfl))
    have hqQ : q ∈ Q := hL q (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨cs', b, hok, hmem⟩ := vote_core P hP hes W hW c t Q hc hQ hterm hfresh hconf X1 hX1 hct1 j
      (hg1 _ hj) (by rw [hjs]; exact hqQ) hjt hjterm
    obtain ⟨-, -, -, -, hcs⟩ := spec_join _ _ _ _ _ hok
    have e_ct : cs'.currentTerm = (X1.node c).currentTerm := by rw [hcs]
    have e_jv : cs'.joinVotes = ((X1.node c).joinVotes.addVote j.sourceNode).1 := by rw [hcs]
    refine ⟨X1.set c cs', .step _ _ _ hX1 (.join X1 c j cs' b (hg1 _ hj) hjt hok), ?_, fun m h => hg1 m h,
      ?_, ?_⟩
    · rw [set_node_self, e_ct]; exact hct1
    · intro x hx; rw [set_node_self, e_jv, addVote_mem]; exact Or.inl (hv1 x hx)
    · intro x hx
      rw [set_node_self]
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [← hjs]; exact hmem
      · rw [e_jv, addVote_mem]; exact Or.inl (hL1 x hx)

/-- A stable election that succeeds: `c` accepts its own start-join request for `t`, every voter not yet in term `t`
accepts it too, and `c` handles every voter's join. -/
private theorem possible_core {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat) (Q : List NodeId) (hc : P.eligible c = true) (hQ : ∀ q ∈ Q, P.eligible q = true)
    (hquorum : (W.node c).lastCommittedConfiguration.hasQuorum Q = true ∧
      (W.node c).lastAcceptedConfiguration.hasQuorum Q = true)
    (hterm : ∀ q, q = c ∨ q ∈ Q → (W.node q).currentTerm < t)
    (hfresh : ∀ q ∈ Q, (W.node q).lastAcceptedTerm < (W.node c).lastAcceptedTerm ∨
      ((W.node q).lastAcceptedTerm = (W.node c).lastAcceptedTerm ∧
        (W.node q).lastAcceptedVersionOrMetadataVersion ≤ (W.node c).lastAcceptedVersionOrMetadataVersion)) :
    ∃ W', ElectionExec P c t Q (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion W W' ∧
      (W'.node c).currentTerm = t ∧ (W'.node c).electionWon = true := by
  have hinv := reachable_inv P hP hes W hW
  have hconf : (W.node c).lastAcceptedConfiguration.isEmpty = false := by
    cases h : (W.node c).lastAcceptedConfiguration.isEmpty
    · rfl
    · have hq := hquorum.2
      rw [hasQuorum_of_isEmpty _ _ h] at hq
      cases hq
  obtain ⟨cs1, j1, h1⟩ := startJoin_ok (W.node c) ⟨P.dn c, t⟩ (hterm c (Or.inl rfl))
  obtain ⟨-, hcs1, hj1⟩ := spec_startJoin _ _ _ _ h1
  have hX0 : ElectionExec P c t Q (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion W
      ((W.set c cs1).send (.join j1)) :=
    .step _ _ _ (.refl W) (.startJoin W c c t cs1 j1 hc (Or.inr ⟨rfl, rfl⟩) h1)
  have hct0 : (((W.set c cs1).send (.join j1)).node c).currentTerm = t := by
    rw [send_node, set_node_self, hcs1]
  have hI0 : ∀ q, q = c ∨ q ∈ Q → (((W.set c cs1).send (.join j1)).node q).currentTerm < t ∨
      ∃ j : Join, ((W.set c cs1).send (.join j1)).sent (.join j) ∧ j.sourceNode.id = q ∧
        j.targetNode.id = c ∧ j.term = t := by
    intro q hq
    by_cases hqc : q = c
    · refine Or.inr ⟨j1, Or.inr rfl, ?_⟩
      rw [hj1, hqc]
      exact ⟨localNode_id hinv c, rfl, rfl⟩
    · left; rw [send_node, set_node_ne _ _ _ _ hqc]; exact hterm q hq
  obtain ⟨X1, hX1, hct1, -, hJ1⟩ := elect_sj_phase P hP hes W hW c t Q hc Q _ hX0 (fun q hq => hq) hct0 hI0
  obtain ⟨X2, hX2, hct2, -, -, hV2⟩ :=
    elect_join_phase P hP hes W hW c t Q hc hQ hterm hfresh hconf Q X1 hX1 (fun q hq => hq) hct1 hJ1
  exact ⟨X2, hX2, hct2, won_core P hP hes W hW c t Q hc hQ hquorum (hterm c (Or.inl rfl)) X2 hX2 hct2 hV2⟩

/-- What the invariant says about the cluster-manager `c` of term `t` that published `s`, of its last published
version: its last published configuration is `s`'s last accepted one, and the only publication of term `t` that it
may still accept is `s` itself. -/
private theorem pub_init {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat)
    (hwon : (W.node c).electionWon = true) (hct : (W.node c).currentTerm = t)
    (s : ClusterState V) (pt : Nat) (pv : Int) (hs : W.sent (.publishRequest c s pt pv)) (hst : s.term = t)
    (hsv : s.version = (W.node c).lastPublishedVersion) :
    (W.node c).lastPublishedConfiguration = s.lastAcceptedConfiguration ∧
    (∀ src s' pt' pv', W.sent (.publishRequest src s' pt' pv') → s'.term = t →
      s' = s ∨ ((W.node c).lastAcceptedTerm = t ∧ s'.version ≤ (W.node c).lastAcceptedVersion)) := by
  have hinv := reachable_inv P hP hes W hW
  have hce : P.eligible c = true := (hinv.pub_wf _ _ _ _ hs).1
  have hpos : 1 ≤ s.term := (hinv.pub_wf _ _ _ _ hs).2.1
  have hle := hinv.term_le c hce
  by_cases hfl : (W.node c).lastPublishedVersion = (W.node c).lastAcceptedVersion
  · rcases hinv.leader_settled c hwon hfl with ⟨hlat, hlpc⟩ | ⟨-, hnone⟩
    · refine ⟨?_, ?_⟩
      · rw [hlpc]
        rcases hinv.accepted_realizes c hce with ⟨h0, -, -⟩ | ⟨h0, -, -⟩ |
            ⟨src', s', pt', pv', hs', h1, h2, h3, -⟩
        · omega
        · omega
        · obtain ⟨-, e, -, -⟩ := hinv.pub_unique _ _ _ _ _ _ _ _ hs hs' (by omega) (by omega)
          rw [h3, e]
      · intro src s' pt' pv' hs' hs't
        right
        refine ⟨by omega, ?_⟩
        have := (hinv.leader_pubs c hwon src s' pt' pv' hs' (by omega)).1
        omega
    · exact absurd (hnone c s pt pv hs) (by omega)
  · obtain ⟨s0, hs0, h0t, h0v, h0lpc, -⟩ := hinv.leader_inflight c hwon hfl
    obtain ⟨-, e, ept, epv⟩ := hinv.pub_unique _ _ _ _ _ _ _ _ hs hs0 (by omega) (by omega)
    refine ⟨by rw [h0lpc, ← e], ?_⟩
    intro src s' pt' pv' hs' hs't
    obtain ⟨hv, hd, -, -⟩ := hinv.leader_pubs c hwon src s' pt' pv' hs' (by omega)
    by_cases hve : s'.version = (W.node c).lastPublishedVersion
    · left
      exact (hinv.pub_unique _ _ _ _ _ _ _ _ hs' hs (by omega) (by omega)).2.1
    · right
      have hd' : Descends W s'.term s'.version s.term s.version := by rw [hst, hsv, ← hct]; exact hd
      have hp := inv_descends_parent P W hinv s'.term s'.version c s pt pv hs hd' (by omega)
      rw [ept, epv] at hp
      rcases inv_descends_key P W hinv _ _ _ _ hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by omega, by omega⟩
      · exact ⟨by omega, by omega⟩

/-- During a stable publication, the cluster-manager `c` stays elected in term `t` with the same last published
version and configuration; its accepted state can only become `s` (every other publication of term `t` is at most
its accepted state), so its configurations stay among its initial ones and `s`'s. -/
private theorem pub_c {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat) (Q : List NodeId)
    (hwon : (W.node c).electionWon = true) (hct : (W.node c).currentTerm = t)
    (s : ClusterState V) (pt : Nat) (pv : Int) (hs : W.sent (.publishRequest c s pt pv)) (hst : s.term = t)
    (hsv : s.version = (W.node c).lastPublishedVersion)
    (W' : Cluster V) (hE : PublicationExec P c t Q W W') :
    (W'.node c).electionWon = true ∧ (W'.node c).currentTerm = t ∧
    (W'.node c).lastPublishedVersion = s.version ∧
    (W'.node c).lastPublishedConfiguration = s.lastAcceptedConfiguration ∧
    ((W'.node c).lastAcceptedConfiguration = (W.node c).lastAcceptedConfiguration ∨
      (W'.node c).lastAcceptedConfiguration = s.lastAcceptedConfiguration) ∧
    ((W'.node c).lastCommittedConfiguration = (W.node c).lastCommittedConfiguration ∨
      (W'.node c).lastCommittedConfiguration = (W.node c).lastAcceptedConfiguration ∨
      (W'.node c).lastCommittedConfiguration = s.lastCommittedConfiguration ∨
      (W'.node c).lastCommittedConfiguration = s.lastAcceptedConfiguration) ∧
    (∀ src s' pt' pv', W'.sent (.publishRequest src s' pt' pv') → s'.term = t →
      s' = s ∨ ((W'.node c).lastAcceptedTerm = t ∧ s'.version ≤ (W'.node c).lastAcceptedVersion)) := by
  have hinv0 := reachable_inv P hP hes W hW
  have hce : P.eligible c = true := (hinv0.pub_wf _ _ _ _ hs).1
  have hpos : 1 ≤ t := hst ▸ (hinv0.pub_wf _ _ _ _ hs).2.1
  obtain ⟨hlpc0, hpr0⟩ := pub_init P hP hes W hW c t hwon hct s pt pv hs hst hsv
  induction hE with
  | refl => exact ⟨hwon, hct, hsv.symm, hlpc0, Or.inl rfl, Or.inl rfl, hpr0⟩
  | step X X' hEX hstep ih =>
    have hinv := reachable_inv P hP hes X (pexec_reach hW hEX)
    obtain ⟨c_ew, c_ct, c_lpv, c_lpc, c_lac, c_lcc, c_pr⟩ := ih
    cases hstep with
    | bootstrap n X0 s0 cs' hX hcontract hconf h =>
      have hn : c ≠ n := by
        intro e
        rw [← e] at h
        obtain ⟨hemp, -⟩ := spec_setInitialState _ _ _ h
        have hq := (hinv.won_quorum _ c_ew).2
        unfold VoteCollection.isQuorum at hq
        rw [hasQuorum_of_isEmpty _ _ hemp] at hq
        cases hq
      rw [set_node_ne _ _ _ _ hn]
      exact ⟨c_ew, c_ct, c_lpv, c_lpc, c_lac, c_lcc, c_pr⟩
    | startJoin n src t' cs' j hsrc hstable h =>
      obtain ⟨hlt, rfl, rfl⟩ := spec_startJoin _ _ _ _ h
      have hn : c ≠ n := by
        intro e
        rw [← e] at hlt hstable
        have := hstable (Or.inl rfl)
        dsimp only at hlt
        omega
      rw [send_node, set_node_ne _ _ _ _ hn]
      refine ⟨c_ew, c_ct, c_lpv, c_lpc, c_lac, c_lcc, ?_⟩
      intro src' s' pt' pv' hs' hs't
      rcases hs' with hs' | hs'
      · exact c_pr src' s' pt' pv' hs' hs't
      · cases hs'
    | join n j cs' b hsent hdest h =>
      obtain ⟨-, -, -, -, rfl⟩ := spec_join _ _ _ _ _ h
      by_cases hn : c = n
      · rw [← hn, set_node_self]
        have hq := hinv.won_quorum _ c_ew
        have hsub : ∀ x, x ∈ (X.node c).joinVotes.nodes →
            x ∈ ((X.node c).joinVotes.addVote j.sourceNode).1.nodes :=
          fun x hx => (addVote_mem _ _ _).mpr (Or.inl hx)
        have hwin : (X.node c).isElectionQuorum P.strategy ((X.node c).joinVotes.addVote j.sourceNode).1 =
            true := by
          rw [hes]
          unfold CoordinationState.isElectionQuorum VoteCollection.isQuorum
          unfold VoteCollection.isQuorum at hq
          rw [quorum_mono _ _ _ hsub hq.1, quorum_mono _ _ _ hsub hq.2]
          rfl
        refine ⟨hwin, c_ct, ?_, c_lpc, c_lac, c_lcc, c_pr⟩
        show (if (X.node c).isElectionQuorum P.strategy ((X.node c).joinVotes.addVote j.sourceNode).1 = true ∧
            (X.node c).electionWon = false then (X.node c).lastAcceptedVersion
            else (X.node c).lastPublishedVersion) = s.version
        rw [if_neg (by intro hc'; rw [c_ew] at hc'; exact absurd hc'.2 (by decide))]
        exact c_lpv
      · rw [set_node_ne _ _ _ _ hn]
        exact ⟨c_ew, c_ct, c_lpv, c_lpc, c_lac, c_lcc, c_pr⟩
    | clientValue n s0 cs' p hn hcontract h =>
      obtain ⟨hew, -, hs0t, -, -, -, rfl, rfl⟩ := spec_clientValue _ _ _ _ h
      rw [send_node, set_node_ne _ _ _ _ (Ne.symm hn)]
      refine ⟨c_ew, c_ct, c_lpv, c_lpc, c_lac, c_lcc, ?_⟩
      intro src' s' pt' pv' hs' hs't
      rcases hs' with hs' | hs'
      · exact c_pr src' s' pt' pv' hs' hs't
      · exfalso
        simp only [Message.publishRequest.injEq] at hs'
        obtain ⟨rfl, rfl, -, -⟩ := hs'
        have hwn : Won P X src' t :=
          ⟨inv_eligible_of_won P X hinv src' hew, Or.inl ⟨hew, by rw [← hs0t]; exact hs't⟩⟩
        have hwc : Won P X c t := ⟨hce, Or.inl ⟨c_ew, c_ct⟩⟩
        exact hn (hinv.won_unique _ _ t hwn hwc)
    | publish n src s0 pt0 pv0 cs' r hsent h =>
      obtain ⟨hst0, hz, rfl, rfl⟩ := spec_publish _ _ _ _ h
      rw [send_node]
      by_cases hn : c = n
      · rw [← hn, set_node_self]
        rw [← hn] at hst0 hz
        dsimp only at hst0 hz
        have hs0t : s0.term = t := by rw [hst0, c_ct]
        have he : s0 = s := by
          rcases c_pr src s0 pt0 pv0 hsent hs0t with he | ⟨h1, h2⟩
          · exact he
          · exfalso
            rcases hz with hz | hz
            · omega
            · exact hz ⟨by omega, h2⟩
        refine ⟨c_ew, c_ct, c_lpv, c_lpc, ?_, ?_, ?_⟩
        · show s0.lastAcceptedConfiguration = _ ∨ s0.lastAcceptedConfiguration = _
          rw [he]; exact Or.inr rfl
        · show s0.lastCommittedConfiguration = _ ∨ s0.lastCommittedConfiguration = _ ∨
            s0.lastCommittedConfiguration = _ ∨ s0.lastCommittedConfiguration = _
          rw [he]; exact Or.inr (Or.inr (Or.inl rfl))
        · intro src' s' pt' pv' hs' hs't
          rcases hs' with hs' | hs'
          · right
            show s0.term = t ∧ s'.version ≤ s0.version
            refine ⟨hs0t, ?_⟩
            have := (hinv.leader_pubs c c_ew src' s' pt' pv' hs' (by omega)).1
            rw [he]; omega
          · cases hs'
      · rw [set_node_ne _ _ _ _ hn]
        refine ⟨c_ew, c_ct, c_lpv, c_lpc, c_lac, c_lcc, ?_⟩
        intro src' s' pt' pv' hs' hs't
        rcases hs' with hs' | hs'
        · exact c_pr src' s' pt' pv' hs' hs't
        · cases hs'
    | respond n src r cs' o hsent h =>
      obtain ⟨-, -, -, rfl, -⟩ := spec_respond _ _ _ _ _ h
      cases o with
      | none =>
        dsimp only
        by_cases hn : c = n
        · rw [← hn, set_node_self]
          exact ⟨c_ew, c_ct, c_lpv, c_lpc, c_lac, c_lcc, c_pr⟩
        · rw [set_node_ne _ _ _ _ hn]
          exact ⟨c_ew, c_ct, c_lpv, c_lpc, c_lac, c_lcc, c_pr⟩
      | some a =>
        dsimp only
        rw [send_node]
        have hpr : ∀ src' s' pt' pv', (X.sent (.publishRequest src' s' pt' pv') ∨
            Message.publishRequest src' s' pt' pv' = Message.applyCommit a) → s'.term = t →
            X.sent (.publishRequest src' s' pt' pv') := by
          intro src' s' pt' pv' hs' _
          rcases hs' with hs' | hs'
          · exact hs'
          · cases hs'
        by_cases hn : c = n
        · rw [← hn, set_node_self]
          exact ⟨c_ew, c_ct, c_lpv, c_lpc, c_lac, c_lcc,
            fun src' s' pt' pv' hs' hs't => c_pr src' s' pt' pv' (hpr _ _ _ _ hs' hs't) hs't⟩
        · rw [set_node_ne _ _ _ _ hn]
          exact ⟨c_ew, c_ct, c_lpv, c_lpc, c_lac, c_lcc,
            fun src' s' pt' pv' hs' hs't => c_pr src' s' pt' pv' (hpr _ _ _ _ hs' hs't) hs't⟩
    | commit n a cs' hsent h =>
      obtain ⟨-, -, -, rfl⟩ := spec_commit _ _ _ h
      by_cases hn : c = n
      · rw [← hn, set_node_self]
        obtain ⟨mt, mv, mlac, mlcc⟩ := markCommitted_spec (X.node c).lastAcceptedState
        refine ⟨c_ew, c_ct, c_lpv, c_lpc, ?_, ?_, ?_⟩
        · show (X.node c).lastAcceptedState.markCommitted.lastAcceptedConfiguration = _ ∨
            (X.node c).lastAcceptedState.markCommitted.lastAcceptedConfiguration = _
          rw [mlac]; exact c_lac
        · show (X.node c).lastAcceptedState.markCommitted.lastCommittedConfiguration = _ ∨
            (X.node c).lastAcceptedState.markCommitted.lastCommittedConfiguration = _ ∨
            (X.node c).lastAcceptedState.markCommitted.lastCommittedConfiguration = _ ∨
            (X.node c).lastAcceptedState.markCommitted.lastCommittedConfiguration = _
          rw [mlcc]
          rcases c_lac with e | e
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr (Or.inr e))
        · intro src' s' pt' pv' hs' hs't
          show s' = s ∨ ((X.node c).lastAcceptedState.markCommitted.term = t ∧
            s'.version ≤ (X.node c).lastAcceptedState.markCommitted.version)
          rw [mt, mv]
          exact c_pr src' s' pt' pv' hs' hs't
      · rw [set_node_ne _ _ _ _ hn]
        exact ⟨c_ew, c_ct, c_lpv, c_lpc, c_lac, c_lcc, c_pr⟩
    | restart n s' hn' hnc hs =>
      rw [set_node_ne _ _ _ _ (Ne.symm hnc)]
      exact ⟨c_ew, c_ct, c_lpv, c_lpc, c_lac, c_lcc, c_pr⟩
    | restartAny n t' s' hn' =>
      have hn : c ≠ n := fun e => by rw [e, hn'] at hce; cases hce
      rw [set_node_ne _ _ _ _ hn]
      exact ⟨c_ew, c_ct, c_lpv, c_lpc, c_lac, c_lcc, c_pr⟩

/-- A node of term `t` either has already acknowledged `(t, v)` to `c` or accepts `s` now: if it rejects `s`, its
accepted state is of term `t` and version at least `v`; that state is a publication of term `t`, hence `c`'s, of
version at most `v` — so exactly `(t, v)`, which it acknowledged to its publisher `c` when accepting it. -/
private theorem pub_q_ready {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (X : Cluster V) (hX : Reachable P X)
    (c : NodeId) (t : Nat) (hw : (X.node c).electionWon = true) (hct : (X.node c).currentTerm = t)
    (s : ClusterState V) (pt : Nat) (pv : Int) (hs : X.sent (.publishRequest c s pt pv)) (hst : s.term = t)
    (hsv : s.version = (X.node c).lastPublishedVersion) (q : NodeId) (hq : P.eligible q = true)
    (hqt : (X.node q).currentTerm = t) :
    X.sent (.publishResponse q c ⟨t, s.version⟩) ∨
      ∃ cs' r, (X.node q).handlePublishRequest ⟨s⟩ = .ok (cs', r) := by
  have hinv := reachable_inv P hP hes X hX
  have hpos : 1 ≤ s.term := (hinv.pub_wf _ _ _ _ hs).2.1
  by_cases hacc : s.term = (X.node q).lastAcceptedTerm ∧ s.version ≤ (X.node q).lastAcceptedVersion
  · left
    obtain ⟨d, hd⟩ := reach_responded P X hX q hq (by omega)
    obtain ⟨s', pt', pv', hs', h1, h2⟩ := hinv.response_published _ _ _ hd
    dsimp only at h1 h2
    have hdc : d = c := hinv.won_unique d c t
      ⟨(hinv.pub_wf _ _ _ _ hs').1, Or.inr ⟨s', pt', pv', hs', by omega⟩⟩
      ⟨(hinv.pub_wf _ _ _ _ hs).1, Or.inr ⟨s, pt, pv, hs, hst⟩⟩
    have hle := (hinv.leader_pubs c hw d s' pt' pv' hs' (by omega)).1
    have hlav : (X.node q).lastAcceptedVersion = s.version := by omega
    have hlat : (X.node q).lastAcceptedTerm = t := by omega
    rw [hlat, hlav, hdc] at hd
    exact hd
  · right
    exact publish_ok (X.node q) s (by omega) hacc

/-- Votes containing `Q` are a publish quorum of the cluster-manager when `Q` is a quorum of its last committed and
last published configurations. -/
private theorem pub_quorum {V : Type} (cs : CoordinationState V) (votes : VoteCollection) (Q : List NodeId)
    (x₁ x₂ x₃ x₄ : VotingConfiguration)
    (hq : x₁.hasQuorum Q = true ∧ x₂.hasQuorum Q = true ∧ x₃.hasQuorum Q = true ∧ x₄.hasQuorum Q = true)
    (hlcc : cs.lastCommittedConfiguration = x₁ ∨ cs.lastCommittedConfiguration = x₂ ∨
      cs.lastCommittedConfiguration = x₃ ∨ cs.lastCommittedConfiguration = x₄)
    (hlpc : cs.lastPublishedConfiguration = x₄) (hsub : ∀ x, x ∈ Q → x ∈ votes.nodes) :
    cs.isPublishQuorum votes = true := by
  unfold CoordinationState.isPublishQuorum VoteCollection.isQuorum
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rcases hlcc with e | e | e | e <;> rw [e]
    · exact quorum_mono _ _ _ hsub hq.1
    · exact quorum_mono _ _ _ hsub hq.2.1
    · exact quorum_mono _ _ _ hsub hq.2.2.1
    · exact quorum_mono _ _ _ hsub hq.2.2.2
  · rw [hlpc]; exact quorum_mono _ _ _ hsub hq.2.2.2

/-- During a stable publication whose cluster-manager `c` had counted no acknowledgement, the publication is
committed as soon as all of `Q` is counted: the acknowledgements are counted only by `c`'s `handlePublishResponse`,
and the one that completes `Q` finds a publish quorum (`Q` is a quorum of every configuration `c` may then use). -/
private theorem commit_track {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat) (Q : List NodeId) (_hQ : ∀ q ∈ Q, P.eligible q = true)
    (hwon : (W.node c).electionWon = true) (hct : (W.node c).currentTerm = t)
    (s : ClusterState V) (pt : Nat) (pv : Int) (hs : W.sent (.publishRequest c s pt pv)) (hst : s.term = t)
    (hsv : s.version = (W.node c).lastPublishedVersion)
    (hquorum : (W.node c).lastCommittedConfiguration.hasQuorum Q = true ∧
      (W.node c).lastAcceptedConfiguration.hasQuorum Q = true ∧
      s.lastCommittedConfiguration.hasQuorum Q = true ∧ s.lastAcceptedConfiguration.hasQuorum Q = true)
    (hpv : (W.node c).publishVotes.nodes = [])
    (W' : Cluster V) (hE : PublicationExec P c t Q W W') :
    Committed W' t s.version ∨ ∃ q ∈ Q, q ∉ (W'.node c).publishVotes.nodes := by
  have hce : P.eligible c = true := ((reachable_inv P hP hes W hW).pub_wf _ _ _ _ hs).1
  induction hE with
  | refl =>
    right
    obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ (ne_nil_of_hasQuorum _ _ hquorum.1)
    exact ⟨q, hq, by rw [hpv]; simp⟩
  | step X X' hEX hstep ih =>
    obtain ⟨c_ew, c_ct, c_lpv, c_lpc, c_lac, c_lcc, -⟩ :=
      pub_c P hP hes W hW c t Q hwon hct s pt pv hs hst hsv X hEX
    rcases ih with hcm | ⟨q, hq, hqn⟩
    · left
      obtain ⟨src, hsrc⟩ := hcm
      exact ⟨src, step_sent (pstep_step hstep) _ hsrc⟩
    · have keep : ∀ cs' : CoordinationState V, cs'.publishVotes = (X.node c).publishVotes →
          ∃ q ∈ Q, q ∉ cs'.publishVotes.nodes := fun cs' e => ⟨q, hq, by rw [e]; exact hqn⟩
      cases hstep with
      | bootstrap n X0 s0 cs' hX hcontract hconf h =>
        obtain ⟨-, rfl⟩ := spec_setInitialState _ _ _ h
        right
        by_cases hn : c = n
        · rw [← hn, set_node_self]; exact keep _ rfl
        · rw [set_node_ne _ _ _ _ hn]; exact keep _ rfl
      | startJoin n src t' cs' j hsrc hstable h =>
        obtain ⟨hlt, rfl, rfl⟩ := spec_startJoin _ _ _ _ h
        have hn : c ≠ n := by
          intro e
          rw [← e] at hlt hstable
          have := hstable (Or.inl rfl)
          dsimp only at hlt
          omega
        right
        rw [send_node, set_node_ne _ _ _ _ hn]; exact keep _ rfl
      | join n j cs' b hsent hdest h =>
        obtain ⟨-, -, -, -, rfl⟩ := spec_join _ _ _ _ _ h
        right
        by_cases hn : c = n
        · rw [← hn, set_node_self]; exact keep _ rfl
        · rw [set_node_ne _ _ _ _ hn]; exact keep _ rfl
      | clientValue n s0 cs' p hn hcontract h =>
        right
        rw [send_node, set_node_ne _ _ _ _ (Ne.symm hn)]; exact keep _ rfl
      | publish n src s0 pt0 pv0 cs' r hsent h =>
        obtain ⟨-, -, rfl, rfl⟩ := spec_publish _ _ _ _ h
        right
        rw [send_node]
        by_cases hn : c = n
        · rw [← hn, set_node_self]; exact keep _ rfl
        · rw [set_node_ne _ _ _ _ hn]; exact keep _ rfl
      | respond n src r cs' o hsent h =>
        obtain ⟨-, hr1, hr2, hcs, -⟩ := spec_respond _ _ _ _ _ h
        by_cases hn : c = n
        · rw [← hn] at h hcs hr1 hr2
          by_cases hall : ∀ x ∈ Q, x ∈ ((X.node c).publishVotes.addVote (P.dn src)).1.nodes
          · left
            have hsub : ∀ x, x ∈ Q → x ∈ ((X.node c).publishVotes.addVote (P.dn src)).1.nodes := hall
            have hpq := pub_quorum (X.node c) _ Q _ _ _ _ hquorum c_lcc c_lpc hsub
            have ho := respond_quorum _ _ _ _ _ h hpq
            subst ho
            dsimp only
            exact ⟨_, Or.inr (by rw [hr1, hr2, c_ct, c_lpv])⟩
          · right
            have hex : ∃ x ∈ Q, x ∉ ((X.node c).publishVotes.addVote (P.dn src)).1.nodes := by
              apply Classical.byContradiction
              intro hne
              apply hall
              intro x hx
              apply Classical.byContradiction
              intro hxn
              exact hne ⟨x, hx, hxn⟩
            cases o with
            | none =>
              dsimp only
              rw [← hn, set_node_self, hcs]; exact hex
            | some a =>
              dsimp only
              rw [send_node, ← hn, set_node_self, hcs]; exact hex
        · right
          cases o with
          | none =>
            dsimp only
            rw [set_node_ne _ _ _ _ hn]; exact keep _ rfl
          | some a =>
            dsimp only
            rw [send_node, set_node_ne _ _ _ _ hn]; exact keep _ rfl
      | commit n a cs' hsent h =>
        obtain ⟨-, -, -, rfl⟩ := spec_commit _ _ _ h
        right
        by_cases hn : c = n
        · rw [← hn, set_node_self]; exact keep _ rfl
        · rw [set_node_ne _ _ _ _ hn]; exact keep _ rfl
      | restart n s' hn' hnc hs =>
        right
        rw [set_node_ne _ _ _ _ (Ne.symm hnc)]; exact keep _ rfl
      | restartAny n t' s' hn' =>
        have hn : c ≠ n := fun e => by rw [e, hn'] at hce; cases hce
        right
        rw [set_node_ne _ _ _ _ hn]; exact keep _ rfl

/-- The acceptance phase of a stable publication: every node of `Q` moves to term `t` if needed and accepts `s`,
unless it has already acknowledged it; afterwards every node of `Q` has acknowledged `(t, v)` to `c`. -/
private theorem pub_accept_phase {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat) (Q : List NodeId) (hQ : ∀ q ∈ Q, P.eligible q = true)
    (hwon : (W.node c).electionWon = true) (hct : (W.node c).currentTerm = t)
    (s : ClusterState V) (pt : Nat) (pv : Int) (hs : W.sent (.publishRequest c s pt pv)) (hst : s.term = t)
    (hsv : s.version = (W.node c).lastPublishedVersion) :
    ∀ (L : List NodeId) (X : Cluster V), PublicationExec P c t Q W X → (∀ q ∈ L, q ∈ Q) →
      (∀ q ∈ Q, (X.node q).currentTerm ≤ t) →
      ∃ X', PublicationExec P c t Q W X' ∧ (∀ m, X.sent m → X'.sent m) ∧
        (∀ q ∈ Q, (X'.node q).currentTerm ≤ t) ∧ ∀ q ∈ L, X'.sent (.publishResponse q c ⟨t, s.version⟩) := by
  have hce : P.eligible c = true := ((reachable_inv P hP hes W hW).pub_wf _ _ _ _ hs).1
  intro L
  induction L with
  | nil => intro X hX _ hT; exact ⟨X, hX, fun _ h => h, hT, fun q hq => by cases hq⟩
  | cons q L ih =>
    intro X hX hL hT
    obtain ⟨X1, hX1, hg1, hT1, hL1⟩ := ih X hX (fun x hx => hL x (List.mem_cons.mpr (Or.inr hx))) hT
    have hqQ : q ∈ Q := hL q (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨X2, hX2, hg2, hT2, hqt⟩ : ∃ X2, PublicationExec P c t Q W X2 ∧ (∀ m, X1.sent m → X2.sent m) ∧
        (∀ q ∈ Q, (X2.node q).currentTerm ≤ t) ∧ (X2.node q).currentTerm = t := by
      by_cases hlt : (X1.node q).currentTerm < t
      · obtain ⟨cs', j, h⟩ := startJoin_ok (X1.node q) ⟨P.dn c, t⟩ hlt
        obtain ⟨-, hcs, -⟩ := spec_startJoin _ _ _ _ h
        have e_ct : cs'.currentTerm = t := by rw [hcs]
        refine ⟨(X1.set q cs').send (.join j),
          .step _ _ _ hX1 (.startJoin X1 q c t cs' j hce (fun _ => Nat.le_refl t) h), fun _ h => Or.inl h, ?_, ?_⟩
        · intro x hx
          rw [send_node]
          by_cases hxq : x = q
          · rw [hxq, set_node_self, e_ct]; exact Nat.le_refl t
          · rw [set_node_ne _ _ _ _ hxq]; exact hT1 x hx
        · rw [send_node, set_node_self, e_ct]
      · exact ⟨X1, hX1, fun _ h => h, hT1, by have := hT1 q hqQ; omega⟩
    have hR2 := pexec_reach hW hX2
    obtain ⟨c_ew, c_ct, c_lpv, -⟩ := pub_c P hP hes W hW c t Q hwon hct s pt pv hs hst hsv X2 hX2
    have hs2 : X2.sent (.publishRequest c s pt pv) := pexec_sent hX2 _ hs
    rcases pub_q_ready P hP hes X2 hR2 c t c_ew c_ct s pt pv hs2 hst c_lpv.symm q (hQ q hqQ) hqt with
      hr | ⟨cs', r, h⟩
    · refine ⟨X2, hX2, fun m hm => hg2 m (hg1 m hm), hT2, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hr
      · exact hg2 _ (hL1 x hx)
    · obtain ⟨-, -, hr, hcs⟩ := spec_publish _ _ _ _ h
      have e_ct : cs'.currentTerm = (X2.node q).currentTerm := by rw [hcs]
      refine ⟨(X2.set q cs').send (.publishResponse q c r),
        .step _ _ _ hX2 (.publish X2 q c s pt pv cs' r hs2 h), fun m hm => Or.inl (hg2 m (hg1 m hm)), ?_, ?_⟩
      · intro x hx
        rw [send_node]
        by_cases hxq : x = q
        · rw [hxq, set_node_self, e_ct]; exact hT2 q hqQ
        · rw [set_node_ne _ _ _ _ hxq]; exact hT2 x hx
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · right
          rw [hr]
          show _ = Message.publishResponse x c ⟨s.term, s.version⟩
          rw [hst]
        · exact Or.inl (hg2 _ (hL1 x hx))

/-- The counting phase of a stable publication: `c` handles the acknowledgement of every node of `Q`, and counts
it. -/
private theorem pub_count_phase {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat) (Q : List NodeId) (hQ : ∀ q ∈ Q, P.eligible q = true)
    (hwon : (W.node c).electionWon = true) (hct : (W.node c).currentTerm = t)
    (s : ClusterState V) (pt : Nat) (pv : Int) (hs : W.sent (.publishRequest c s pt pv)) (hst : s.term = t)
    (hsv : s.version = (W.node c).lastPublishedVersion) :
    ∀ (L : List NodeId) (X : Cluster V), PublicationExec P c t Q W X → (∀ q ∈ L, q ∈ Q) →
      (∀ q ∈ L, X.sent (.publishResponse q c ⟨t, s.version⟩)) →
      ∃ X', PublicationExec P c t Q W X' ∧ (∀ m, X.sent m → X'.sent m) ∧
        (∀ x, x ∈ (X.node c).publishVotes.nodes → x ∈ (X'.node c).publishVotes.nodes) ∧
        ∀ q ∈ L, q ∈ (X'.node c).publishVotes.nodes := by
  intro L
  induction L with
  | nil => intro X hX _ _; exact ⟨X, hX, fun _ h => h, fun _ h => h, fun q hq => by cases hq⟩
  | cons q L ih =>
    intro X hX hL hR
    obtain ⟨X1, hX1, hg1, hv1, hL1⟩ := ih X hX (fun x hx => hL x (List.mem_cons.mpr (Or.inr hx)))
      (fun x hx => hR x (List.mem_cons.mpr (Or.inr hx)))
    have hqQ : q ∈ Q := hL q (List.mem_cons.mpr (Or.inl rfl))
    have hr1 : X1.sent (.publishResponse q c ⟨t, s.version⟩) := hg1 _ (hR q (List.mem_cons.mpr (Or.inl rfl)))
    obtain ⟨c_ew, c_ct, c_lpv, -⟩ := pub_c P hP hes W hW c t Q hwon hct s pt pv hs hst hsv X1 hX1
    obtain ⟨cs', o, h, -⟩ := respond_ok (X1.node c) (P.dn q) ⟨t, s.version⟩ c_ew c_ct.symm c_lpv.symm
    obtain ⟨-, -, -, hcs, -⟩ := spec_respond _ _ _ _ _ h
    have e_pv : cs'.publishVotes = ((X1.node c).publishVotes.addVote (P.dn q)).1 := by rw [hcs]
    have hgrow : ∀ x, x ∈ (X.node c).publishVotes.nodes → x ∈ cs'.publishVotes.nodes := by
      intro x hx; rw [e_pv, addVote_mem]; exact Or.inl (hv1 x hx)
    have hall : ∀ x ∈ q :: L, x ∈ cs'.publishVotes.nodes := by
      intro x hx
      rw [e_pv, addVote_mem]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inr ⟨rfl, hQ x hqQ⟩
      · exact Or.inl (hL1 x hx)
    cases o with
    | none =>
      refine ⟨X1.set c cs', .step _ _ _ hX1 (.respond X1 c q ⟨t, s.version⟩ cs' none hr1 h),
        fun m hm => hg1 m hm, ?_, ?_⟩
      · intro x hx; rw [set_node_self]; exact hgrow x hx
      · intro x hx; rw [set_node_self]; exact hall x hx
    | some a =>
      refine ⟨(X1.set c cs').send (.applyCommit a),
        .step _ _ _ hX1 (.respond X1 c q ⟨t, s.version⟩ cs' (some a) hr1 h), fun m hm => Or.inl (hg1 m hm), ?_, ?_⟩
      · intro x hx; rw [send_node, set_node_self]; exact hgrow x hx
      · intro x hx; rw [send_node, set_node_self]; exact hall x hx

/-- A stable publication that is committed: after the acceptance and counting phases, one more acknowledgement
handled by `c` finds a publish quorum and sends the commit. -/
private theorem pub_possible_core {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat) (Q : List NodeId) (hQ : ∀ q ∈ Q, P.eligible q = true)
    (hwon : (W.node c).electionWon = true) (hct : (W.node c).currentTerm = t)
    (s : ClusterState V) (pt : Nat) (pv : Int) (hs : W.sent (.publishRequest c s pt pv)) (hst : s.term = t)
    (hsv : s.version = (W.node c).lastPublishedVersion)
    (hquorum : (W.node c).lastCommittedConfiguration.hasQuorum Q = true ∧
      (W.node c).lastAcceptedConfiguration.hasQuorum Q = true ∧
      s.lastCommittedConfiguration.hasQuorum Q = true ∧ s.lastAcceptedConfiguration.hasQuorum Q = true)
    (hterm : ∀ q ∈ Q, (W.node q).currentTerm ≤ t) :
    ∃ W', PublicationExec P c t Q W W' ∧ Committed W' t s.version := by
  obtain ⟨X1, hX1, -, -, hR1⟩ := pub_accept_phase P hP hes W hW c t Q hQ hwon hct s pt pv hs hst hsv Q W
    (.refl W) (fun q hq => hq) hterm
  obtain ⟨X2, hX2, hg2, -, hV2⟩ := pub_count_phase P hP hes W hW c t Q hQ hwon hct s pt pv hs hst hsv Q X1 hX1
    (fun q hq => hq) hR1
  obtain ⟨q0, hq0⟩ := List.exists_mem_of_ne_nil _ (ne_nil_of_hasQuorum _ _ hquorum.1)
  obtain ⟨c_ew, c_ct, c_lpv, c_lpc, -, c_lcc, -⟩ := pub_c P hP hes W hW c t Q hwon hct s pt pv hs hst hsv X2 hX2
  have hr : X2.sent (.publishResponse q0 c ⟨t, s.version⟩) := hg2 _ (hR1 q0 hq0)
  obtain ⟨cs', o, h, hsome⟩ := respond_ok (X2.node c) (P.dn q0) ⟨t, s.version⟩ c_ew c_ct.symm c_lpv.symm
  have hsub : ∀ x, x ∈ Q → x ∈ ((X2.node c).publishVotes.addVote (P.dn q0)).1.nodes :=
    fun x hx => (addVote_mem _ _ _).mpr (Or.inl (hV2 x hx))
  have ho := hsome (pub_quorum _ _ Q _ _ _ _ hquorum c_lcc c_lpc hsub)
  subst ho
  exact ⟨_, .step _ _ _ hX2 (.respond X2 c q0 ⟨t, s.version⟩ cs' _ hr h), ⟨_, Or.inr rfl⟩⟩

/-- **Stable publications are committed.** Under the hypotheses of `publication_committed` (except that `c` may already
have counted acknowledgements), with the nodes of `Q` in terms at most `t`, there is a stable publication execution at
the end of which the publication is committed. Only the existence is stated; in the witness, each node of `Q` moves to
term `t` if needed and accepts and acknowledges the publication unless it already has, and `c` counts the
acknowledgements. -/
theorem solution {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat) (Q : List NodeId) (hQ : ∀ q ∈ Q, P.eligible q = true)
    (hwon : (W.node c).electionWon = true) (hct : (W.node c).currentTerm = t)
    (s : ClusterState V) (pt : Nat) (pv : Int) (hs : W.sent (.publishRequest c s pt pv)) (hst : s.term = t)
    (hsv : s.version = (W.node c).lastPublishedVersion)
    (hquorum : (W.node c).lastCommittedConfiguration.hasQuorum Q = true ∧
      (W.node c).lastAcceptedConfiguration.hasQuorum Q = true ∧
      s.lastCommittedConfiguration.hasQuorum Q = true ∧ s.lastAcceptedConfiguration.hasQuorum Q = true)
    (hterm : ∀ q ∈ Q, (W.node q).currentTerm ≤ t) :
    ∃ W', PublicationExec P c t Q W W' ∧ Committed W' t s.version := by
  exact pub_possible_core P hP hes W hW c t Q hQ hwon hct s pt pv hs hst hsv hquorum hterm

-- Prove2me | solution 1 for OpenSearchCoordination.handleJoin_spec
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:49:57.122784+00:00
-- url     : https://prove2.me/submissions/85513a4d-3097-4c90-8a2e-10b1e7f98ba1

import Definitions.Def_OpenSearchCoordination

open OpenSearchCoordination

/-- Counting: an element satisfying both `p` and `q` is counted at most twice on the left and once on each side. -/
private theorem filter_length_add_le {α : Type} (L : List α) (p q : α → Bool) :
    (L.filter p).length + (L.filter q).length ≤ L.length + (L.filter (fun x => p x && q x)).length := by
  induction L with
  | nil => simp
  | cons y ys ih =>
    cases hp : p y <;> cases hq : q y <;> simp [hp, hq] <;> omega

/-- Filtering by a weaker predicate keeps at least as many elements. -/
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

/-- A node only counts the vote of a voter whose last accepted state is no fresher than its own: `handleJoin` succeeds
only if the join is for the current term, the node has started a join since its last reboot, it has been bootstrapped,
and the voter's (accepted term, version) is lexicographically at most the node's (accepted term, version-or-metadata
version). After a successful join, `electionWon` is exactly whether the votes form an election quorum. -/
theorem solution {V : Type} (es : ElectionStrategy) (cs : CoordinationState V) (j : Join) (cs' : CoordinationState V)
    (b : Bool) (h : cs.handleJoin es j = .ok (cs', b)) :
    j.term = cs.currentTerm ∧ cs.startedJoinSinceLastReboot = true ∧
    cs.lastAcceptedConfiguration.isEmpty = false ∧
    (j.lastAcceptedTerm < cs.lastAcceptedTerm ∨
      (j.lastAcceptedTerm = cs.lastAcceptedTerm ∧ j.lastAcceptedVersion ≤ cs.lastAcceptedVersionOrMetadataVersion)) ∧
    cs'.joinVotes = (cs.joinVotes.addVote j.sourceNode).1 ∧ b = (cs.joinVotes.addVote j.sourceNode).2 ∧
    cs'.electionWon = cs.isElectionQuorum es cs'.joinVotes ∧
    cs'.currentTerm = cs.currentTerm ∧ cs'.lastAcceptedState = cs.lastAcceptedState ∧
    cs'.localNode = cs.localNode ∧ cs'.startedJoinSinceLastReboot = cs.startedJoinSinceLastReboot ∧
    cs'.publishVotes = cs.publishVotes ∧ cs'.lastPublishedConfiguration = cs.lastPublishedConfiguration ∧
    cs'.lastPublishedVersion =
      (if cs'.electionWon = true ∧ cs.electionWon = false then cs.lastAcceptedVersion else cs.lastPublishedVersion) := by
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
  generalize hva : cs.joinVotes.addVote j.sourceNode = va at h
  obtain ⟨votes, added⟩ := va
  dsimp only at h
  split at h
  · rename_i hw
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [Bool.and_eq_true, Bool.not_eq_true'] at hw
    exact ⟨h1', h2', h5', hlex, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [hw]⟩
  · rename_i hw
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [Bool.and_eq_true, Bool.not_eq_true'] at hw
    exact ⟨h1', h2', h5', hlex, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [hw]⟩

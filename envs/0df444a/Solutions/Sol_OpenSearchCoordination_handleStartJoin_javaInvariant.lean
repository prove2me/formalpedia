-- Prove2me | solution 1 for OpenSearchCoordination.handleStartJoin_javaInvariant
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:50:25.283236+00:00
-- url     : https://prove2.me/submissions/c9a262ec-73de-41ee-b6af-c8259c1fcd9e

import Definitions.Def_OpenSearchCoordination
import Theorems.Thm_OpenSearchCoordination_handleStartJoin_spec
import Theorems.Thm_OpenSearchCoordination_no_votes_no_quorum

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

/-- `handleStartJoin` re-establishes `invariant()` from any state whose accepted term is at most its current term. -/
theorem solution {V : Type} (es : ElectionStrategy) (cs : CoordinationState V) (r : StartJoinRequest)
    (cs' : CoordinationState V) (j : Join) (hcs : cs.lastAcceptedTerm ≤ cs.currentTerm)
    (h : cs.handleStartJoin r = .ok (cs', j)) : cs'.javaInvariant es := by
  obtain ⟨hlt, h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := (handleStartJoin_spec cs r cs' j).1 h
  unfold CoordinationState.javaInvariant
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold CoordinationState.lastAcceptedTerm at hcs ⊢
    rw [h2, h1]
    omega
  · unfold CoordinationState.isElectionQuorum
    rw [h5, h6, no_votes_no_quorum]
    rfl
  · rw [h5, h8]
    rfl
  · rw [h5]
    intro h
    cases h
  · left
    rw [h7]
    rfl

-- Prove2me | solution 1 for OpenSearchCoordination.empty_no_quorum
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:49:53.14385+00:00
-- url     : https://prove2.me/submissions/f279c102-b322-495a-a537-0703e0241748

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

/-- The empty configuration has no quorum; a node whose configurations are empty can never win an election. -/
theorem solution (a : List NodeId) : VotingConfiguration.EMPTY_CONFIG.hasQuorum a = false := by
  rfl

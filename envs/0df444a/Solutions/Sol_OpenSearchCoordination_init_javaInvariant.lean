-- Prove2me | solution 1 for OpenSearchCoordination.init_javaInvariant
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:50:24.542907+00:00
-- url     : https://prove2.me/submissions/471d43b6-9270-4958-a743-a7cbd0b2c329

import Definitions.Def_OpenSearchCoordination
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

/-- A freshly constructed (restarted) node satisfies `invariant()` whenever its persisted accepted term is at most its
persisted current term. -/
theorem solution {V : Type} (es : ElectionStrategy) (n : DiscoveryNode) (t : Nat) (s : ClusterState V)
    (h : s.term ≤ t) : (CoordinationState.init n t s).javaInvariant es := by
  unfold CoordinationState.javaInvariant
  refine ⟨h, ?_, rfl, (fun h => by cases h), Or.inl rfl⟩
  unfold CoordinationState.isElectionQuorum CoordinationState.init
  dsimp only
  rw [no_votes_no_quorum]
  rfl

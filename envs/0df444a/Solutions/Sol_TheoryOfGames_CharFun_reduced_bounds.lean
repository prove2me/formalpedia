-- Prove2me | solution 1 for TheoryOfGames.CharFun.reduced_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T12:27:33.382905+00:00
-- url     : https://prove2.me/submissions/1ee9ea65-9648-4198-9e4d-5978c8dcb974

import Mathlib
import Definitions.Def_TheoryOfGames_CharFun_IsCharFunction
import Definitions.Def_TheoryOfGames_CharFun_StrategicEquivalence

set_option autoImplicit false

open TheoryOfGames.CharFun in
theorem reduced_bounds_lower_aux {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v)
    (γ : ℝ) (hγ : ∀ k : Fin n, v {k} = -γ) :
    ∀ S : Finset (Fin n), -((S.card : ℝ) * γ) ≤ v S := by
  intro S
  induction S using Finset.induction_on with
  | empty => simp [hv.1]
  | insert a S ha ih =>
    have hd : Disjoint ({a} : Finset (Fin n)) S := Finset.disjoint_singleton_left.mpr ha
    have h3 := hv.2.2 {a} S hd
    rw [Finset.card_insert_of_notMem ha]
    rw [← Finset.insert_eq] at h3
    rw [hγ a] at h3
    push_cast
    linarith

open TheoryOfGames.CharFun in
theorem reduced_bounds_card_compl {n : ℕ} (S : Finset (Fin n)) :
    ((Sᶜ.card : ℕ) : ℝ) = (n : ℝ) - S.card := by
  have h := Finset.card_compl_add_card S
  rw [Fintype.card_fin] at h
  have h' : ((Sᶜ.card : ℕ) : ℝ) + (S.card : ℝ) = (n : ℝ) := by exact_mod_cast h
  linarith

namespace TheoryOfGames.CharFun

/-- (27:7), (27:7*), (27:7**): let `v̄` be a reduced characteristic function and `γ` the number
with (27:5) `-γ = v̄((1)) = ⋯ = v̄((n))`. Then for every `p`-element set `S`
`-pγ ≤ v̄(S) ≤ (n - p)γ`; for `p = 0, 1` the first relation is an equality, and for
`p = n - 1, n` the second relation is an equality. -/
theorem reduced_bounds_main {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v)
    (hred : IsReduced v) (γ : ℝ) (hγ : ∀ k : Fin n, v {k} = -γ) :
    (∀ S : Finset (Fin n),
        -((S.card : ℝ) * γ) ≤ v S ∧ v S ≤ ((n : ℝ) - S.card) * γ) ∧
      (∀ S : Finset (Fin n), S.card ≤ 1 → v S = -((S.card : ℝ) * γ)) ∧
      (∀ S : Finset (Fin n), n ≤ S.card + 1 → v S = ((n : ℝ) - S.card) * γ) := by
  have low := reduced_bounds_lower_aux v hv γ hγ
  have small : ∀ S : Finset (Fin n), S.card ≤ 1 → v S = -((S.card : ℝ) * γ) := by
    intro S hS
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hS with h0 | h1
    · rw [Finset.card_eq_zero.mp h0]; simp [hv.1]
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
      simp [hγ a]
  refine ⟨?_, small, ?_⟩
  · intro S
    refine ⟨low S, ?_⟩
    have h1 := low Sᶜ
    have h2 := hv.2.1 S
    rw [reduced_bounds_card_compl] at h1
    linarith
  · intro S hS
    have hc : Sᶜ.card ≤ 1 := by
      have h := Finset.card_compl_add_card S
      rw [Fintype.card_fin] at h
      omega
    have h1 := small Sᶜ hc
    have h2 := hv.2.1 S
    rw [reduced_bounds_card_compl] at h1
    linarith

end TheoryOfGames.CharFun

open TheoryOfGames.CharFun in
theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v)
    (hred : IsReduced v) (γ : ℝ) (hγ : ∀ k : Fin n, v {k} = -γ) :
    (∀ S : Finset (Fin n),
        -((S.card : ℝ) * γ) ≤ v S ∧ v S ≤ ((n : ℝ) - S.card) * γ) ∧
      (∀ S : Finset (Fin n), S.card ≤ 1 → v S = -((S.card : ℝ) * γ)) ∧
      (∀ S : Finset (Fin n), n ≤ S.card + 1 → v S = ((n : ℝ) - S.card) * γ) := by
  exact TheoryOfGames.CharFun.reduced_bounds_main v hv hred γ hγ

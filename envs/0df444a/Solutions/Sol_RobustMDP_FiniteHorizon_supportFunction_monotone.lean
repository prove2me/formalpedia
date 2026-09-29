-- Prove2me | solution 1 for RobustMDP.FiniteHorizon.supportFunction_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T22:25:29.416131+00:00
-- url     : https://prove2.me/submissions/591d3532-5e55-40a7-a388-ea1d90df432f

import Mathlib
import Definitions.Def_RobustMDP_Shared_supportFunction

open RobustMDP

theorem solution {n : ℕ} (S : Set (Fin n → ℝ)) (hS : S ⊆ stdSimplex ℝ (Fin n))
    (hne : S.Nonempty) : Monotone (Shared.supportFunction S) := by
  have hbdd : ∀ u : Fin n → ℝ,
      BddAbove ((fun p : Fin n → ℝ => ∑ j, p j * u j) '' S) := by
    intro u
    refine ⟨∑ j, |u j|, ?_⟩
    rintro z ⟨p, hpS, rfl⟩
    obtain ⟨hpnn, hpsum⟩ := hS hpS
    have hple : ∀ j, p j ≤ 1 := by
      intro j
      have h := Finset.single_le_sum (f := p) (fun i _ => hpnn i) (Finset.mem_univ j)
      rw [hpsum] at h
      exact h
    calc ∑ j, p j * u j ≤ ∑ j, p j * |u j| :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (le_abs_self _) (hpnn j)
      _ ≤ ∑ j, 1 * |u j| :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hple j) (abs_nonneg _)
      _ = ∑ j, |u j| := by simp
  intro v w hvw
  refine csSup_le (Set.Nonempty.image _ hne) ?_
  rintro z ⟨p, hpS, rfl⟩
  obtain ⟨hpnn, hpsum⟩ := hS hpS
  have h1 : ∑ j, p j * v j ≤ ∑ j, p j * w j :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hvw j) (hpnn j)
  exact h1.trans (le_csSup (hbdd w) ⟨p, hpS, rfl⟩)

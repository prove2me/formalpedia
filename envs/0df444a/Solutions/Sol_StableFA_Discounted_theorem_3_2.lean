-- Prove2me | solution 1 for StableFA.Discounted.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:11:04.122345+00:00
-- url     : https://prove2.me/submissions/e6fb3ce1-c752-4bef-bc44-2b28211c54e7

import Mathlib
import Definitions.Def_BertsekasSSPModel
import Definitions.Def_StableFA_Discounted_Setting
import Theorems.Thm_StableFA_Discounted_theorem_3_1

open Filter Topology
open StableFA.Discounted


theorem solution {n : ℕ} (A : Averager n) :
    (∀ Y Z : Fin n → ℝ, ‖A.apply Y - A.apply Z‖ ≤ ‖Y - Z‖) ∧
    ∀ (C : Type) [Fintype C] (M : BertsekasSSPModel n C) (γ : ℝ), 0 ≤ γ → γ < 1 →
      (∀ i, ∀ u ∈ M.U i, ∑ j, M.p i u j = 1) →
      Compatible A.apply (BertsekasDiscountedBellmanOp M γ) := by
  have hn (Y Z : Fin n → ℝ) : ‖A.apply Y - A.apply Z‖ ≤ ‖Y-Z‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro i
    have hs : ∑ j, A.β i j ≤ 1 := by linarith [A.sum_eq_one i, A.βc_nonneg i]
    change ‖(A.βc i * A.k i + ∑ j, A.β i j * Y j) -
      (A.βc i * A.k i + ∑ j, A.β i j * Z j)‖ ≤ _
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    calc
      ‖∑ j, (A.β i j * Y j - A.β i j * Z j)‖ ≤
          ∑ j, ‖A.β i j * Y j - A.β i j * Z j‖ := norm_sum_le _ _
      _ ≤ ∑ j, A.β i j * ‖Y-Z‖ := by
        apply Finset.sum_le_sum
        intro j hj
        rw [← mul_sub, norm_mul, Real.norm_of_nonneg (A.β_nonneg i j)]
        exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm (Y-Z) j) (A.β_nonneg i j)
      _ = (∑ j, A.β i j) * ‖Y-Z‖ := (Finset.sum_mul ..).symm
      _ ≤ ‖Y-Z‖ := by nlinarith [norm_nonneg (Y-Z)]
  exact ⟨hn, fun C _ M γ hγ0 hγ1 hp1 => (theorem_3_1 M γ hγ0 hγ1 hp1 A.apply hn).1⟩



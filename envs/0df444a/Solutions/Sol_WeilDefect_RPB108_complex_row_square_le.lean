-- Prove2me | solution 1 for WeilDefect.RPB108.complex_row_square_le
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:27:47.935553+00:00
-- url     : https://prove2.me/submissions/526c7fe5-1638-45b4-8da4-3b435acb992a

import Theorems.Thm_WeilDefect_RPB108_weighted_mass_sq_le_energy
import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem solution {ι : Type*} [Fintype ι]
    (a z : ι → ℂ) (b : ι → ℝ) (hb : ∀ i, ‖a i‖ ≤ b i) :
    ‖∑ i, a i*z i‖^2 ≤ (∑ i, (b i)^2)*(∑ i, ‖z i‖^2) := by
  have ht : ‖∑ i, a i*z i‖ ≤ ∑ i, b i*‖z i‖ := by
    calc
      ‖∑ i, a i*z i‖ ≤ ∑ i, ‖a i*z i‖ := norm_sum_le _ _
      _ ≤ ∑ i, b i*‖z i‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hb i) (norm_nonneg _)
  have hn : 0 ≤ ∑ i, b i*‖z i‖ := (norm_nonneg _).trans ht
  have hs : ‖∑ i, a i*z i‖^2 ≤ (∑ i, b i*‖z i‖)^2 := by
    nlinarith only [ht, hn, norm_nonneg (∑ i, a i*z i)]
  have hc := weighted_mass_sq_le_energy Finset.univ b (fun _ => 1)
    (fun i => ‖z i‖) (by intros; norm_num)
  simp only [Finset.mem_univ, forall_const, one_mul, div_one,
    abs_of_nonneg (norm_nonneg _)] at hc
  exact hs.trans hc

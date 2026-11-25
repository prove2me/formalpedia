-- Prove2me | solution 1 for PI.EF.sum_pTerm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:04:47.23734+00:00
-- url     : https://prove2.me/submissions/d286fb8c-2798-453f-a15a-d028ef113edd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSumBound
import Theorems.Thm_PI_EF_nearB_nonneg
import Theorems.Thm_PI_EF_sum_inv_le
import Theorems.Thm_PI_EF_sum_nearB
import Theorems.Thm_PI_EF_pTerm_le
import Theorems.Thm_PI_EF_logTerm_nonneg
import Theorems.Thm_PI_EF_log_ge_half
import Theorems.Thm_PI_EF_sum_logTerm_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Finset
namespace PI.EF
theorem _root_.solution {u T : ℝ} (hu : 2 ≤ u) (hT : 2 ≤ T) (K : ℕ) :
    ∑ n ∈ range K, pTerm u T n ≤ 500 * (u * Real.log u ^ 2 / T + Real.log u) := by
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hL := log_ge_half hu
  set L := Real.log u with hLdef
  have h1 : ∑ n ∈ range K, pTerm u T n ≤ (4 * Real.exp 1 * u / T) * ∑ n ∈ range K, logTerm (cLine u) n +
      16 * L * ∑ n ∈ range K, (if n < ⌊u⌋₊ + (⌊u⌋₊ + 2) then nearB u T n else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun n _ => pTerm_le hu hT0 n)
  have hc : cLine u = 1 + 2 * (1 / (2 * L)) := by
    unfold cLine
    rw [← hLdef]
    field_simp
  have h2 : ∑ n ∈ range K, logTerm (cLine u) n ≤ 4 * L ^ 2 := by
    rw [hc]
    refine (sum_logTerm_le (by positivity) K).trans (le_of_eq ?_)
    field_simp
    norm_num
  have h3 : ∑ n ∈ range K, (if n < ⌊u⌋₊ + (⌊u⌋₊ + 2) then nearB u T n else 0) ≤
      4 + 2 * ((4 * u / T) * (3 * L)) := by
    rw [← Finset.sum_filter]
    have hsub : (range K).filter (fun n => n < ⌊u⌋₊ + (⌊u⌋₊ + 2)) ⊆ range (⌊u⌋₊ + (⌊u⌋₊ + 2)) := by
      intro n hn
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hn).2
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n _ _ => nearB_nonneg hu0 hT0 n)).trans ?_
    rw [sum_nearB]
    have h4 := sum_inv_le ⌊u⌋₊
    have h5 : Real.log (⌊u⌋₊ : ℝ) ≤ L := by
      apply Real.log_le_log
      · exact_mod_cast Nat.floor_pos.mpr (by linarith : (1 : ℝ) ≤ u)
      · exact Nat.floor_le hu0.le
    have h6 : ∑ j ∈ range ⌊u⌋₊, 1 / ((j : ℝ) + 1) ≤ 3 * L := by linarith
    have h7 : (4 * u / T) * ∑ j ∈ range ⌊u⌋₊, 1 / ((j : ℝ) + 1) ≤ (4 * u / T) * (3 * L) :=
      mul_le_mul_of_nonneg_left h6 (by positivity)
    linarith
  have he : Real.exp 1 < 3 := Real.exp_one_lt_three
  have huT : 0 < u / T := by positivity
  have k1 : (4 * Real.exp 1 * u / T) * ∑ n ∈ range K, logTerm (cLine u) n ≤
      (4 * 3 * (u / T)) * (4 * L ^ 2) := by
    have q1 : 4 * Real.exp 1 * u / T ≤ 4 * 3 * (u / T) := by
      have : 4 * Real.exp 1 * u / T = 4 * Real.exp 1 * (u / T) := by ring
      rw [this]
      nlinarith
    exact mul_le_mul q1 h2 (Finset.sum_nonneg (fun n _ => logTerm_nonneg _ n)) (by positivity)
  have k2 : 16 * L * ∑ n ∈ range K, (if n < ⌊u⌋₊ + (⌊u⌋₊ + 2) then nearB u T n else 0) ≤
      16 * L * (4 + 2 * ((4 * u / T) * (3 * L))) := mul_le_mul_of_nonneg_left h3 (by linarith)
  have k3 : u * L ^ 2 / T = (u / T) * L ^ 2 := by ring
  have k4 : 4 * u / T = 4 * (u / T) := by ring
  rw [k3]
  rw [k4] at k2
  have k5 : 0 ≤ (u / T) * L ^ 2 := by positivity
  nlinarith
end PI.EF

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Elem_prime_partial_le_66a4bd05bbf2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:35:14.290465+00:00
-- url     : https://prove2.me/submissions/7dfd66d4-7200-44df-9d3e-e668e9517c91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PrimeWeightEqZeroOfLt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_primeWeight_nonneg_6255b916e79a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_sum_primeWeight_le_932b2b356f63
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_primeWeight_eq_zero_of_lt_0f940253db51
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_abel_step_2c0219849098

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.Elem
namespace GroundTheory.Heights₂.Heights.RestTerms.Elem
theorem _root_.solution (B : ℝ) (hB : 0 < B) (K : ℕ) :
    ∑ i ∈ range K, primeWeight B i / (i : ℝ) ^ 2 ≤ 2 * Real.log 4 / B := by
  set M := ⌊B⌋₊ + 1 with hM
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hMB : B < (M : ℝ) := by
    rw [hM]; push_cast; exact Nat.lt_floor_add_one B
  have hMpos : (0 : ℝ) < M := lt_trans hB hMB
  have hfinal : 2 * Real.log 4 / (M : ℝ) ≤ 2 * Real.log 4 / B :=
    div_le_div_of_nonneg_left (by positivity) hB hMB.le
  rcases lt_or_ge K M with hK | hK
  · rw [Finset.sum_eq_zero]
    · positivity
    · intro i hi
      rw [primeWeight_eq_zero_of_lt B hB.le (lt_trans (Finset.mem_range.mp hi) hK), zero_div]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hK
    have hW := abel_step B hB j
    rw [← hM] at hW
    set K := M + j
    have hKpos : (0 : ℝ) < (K : ℝ) := by
      have : (M : ℝ) ≤ K := by exact_mod_cast (Nat.le_add_right M j)
      linarith
    have hG : ∑ i ∈ range K, primeWeight B i ≤ K * Real.log 4 := by
      calc ∑ i ∈ range K, primeWeight B i ≤ ∑ i ∈ range (K + 1), primeWeight B i :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
              (fun i _ _ => primeWeight_nonneg B i)
        _ ≤ K * Real.log 4 := sum_primeWeight_le B K
    have hGK : (∑ i ∈ range K, primeWeight B i) / (K : ℝ) ^ 2 ≤ Real.log 4 / K := by
      rw [div_le_div_iff₀ (by positivity) hKpos]
      nlinarith
    have h1 : 0 ≤ Real.log 4 / K := by positivity
    calc ∑ i ∈ range K, primeWeight B i / (i : ℝ) ^ 2
        ≤ 2 * Real.log 4 * (1 / (M : ℝ) - 1 / (K : ℝ)) + Real.log 4 / K := by linarith
      _ = 2 * Real.log 4 / (M : ℝ) - Real.log 4 / K := by ring
      _ ≤ 2 * Real.log 4 / (M : ℝ) := by linarith
      _ ≤ 2 * Real.log 4 / B := hfinal
end GroundTheory.Heights₂.Heights.RestTerms.Elem

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Elem_int_partial_le_78baa4e70c2b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:24:25.075374+00:00
-- url     : https://prove2.me/submissions/55359f58-5d6a-4ba0-a1b2-ee4fc5c23135

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PrimeWeightEqZeroOfLt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_phiT_nonneg_7a19d717162f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_intWeight_nonneg_546dc8b33f2f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_int_step_09746dc8c802

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
theorem _root_.solution (B₀ : ℝ) (hB : 16 ≤ B₀) (K : ℕ) :
    ∑ m ∈ range K, intWeight B₀ m ≤ 2 * (1 + Real.log B₀) / B₀ := by
  set n := ⌊B₀⌋₊ with hn
  have hB0 : 0 < B₀ := by linarith
  have hn16 : 16 ≤ n := by
    rw [hn]; exact Nat.le_floor (by exact_mod_cast hB)
  have hnle : (n : ℝ) ≤ B₀ := Nat.floor_le hB0.le
  have hnlt : B₀ < (n : ℝ) + 1 := Nat.lt_floor_add_one B₀
  have hn1 : (16 : ℝ) ≤ n := by exact_mod_cast hn16
  have hphi : phiT n ≤ 2 * (1 + Real.log B₀) / B₀ := by
    unfold phiT
    have hlog : Real.log n ≤ Real.log B₀ := Real.log_le_log (by linarith) hnle
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    rw [div_le_div_iff₀ (by linarith) hB0]
    nlinarith
  have hS : ∀ K, ∑ m ∈ range K, intWeight B₀ m ≤ phiT n := by
    intro K
    rcases le_or_gt K (n + 1) with hK | hK
    · calc ∑ m ∈ range K, intWeight B₀ m ≤ ∑ m ∈ range (n + 1 + 0), intWeight B₀ m :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
              (fun m _ _ => intWeight_nonneg B₀ m)
        _ ≤ phiT n - phiT ((n + 0 : ℕ) : ℝ) := int_step B₀ hB 0
        _ ≤ phiT n := by
            have := phiT_nonneg (t := ((n + 0 : ℕ) : ℝ)) (by push_cast; linarith)
            linarith
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hK.le
      calc ∑ m ∈ range (n + 1 + j), intWeight B₀ m ≤ phiT n - phiT ((n + j : ℕ) : ℝ) :=
            int_step B₀ hB j
        _ ≤ phiT n := by
            have := phiT_nonneg (t := ((n + j : ℕ) : ℝ)) (by push_cast; linarith)
            linarith
  exact (hS K).trans hphi
end GroundTheory.Heights₂.Heights.RestTerms.Elem

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_IntegerLogSquareTail_intersectionNumber_baseChange_ca98df2fb43b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:38:30.603683+00:00
-- url     : https://prove2.me/submissions/1435e980-fe23-4109-a34e-4b5032909593

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PrimeWeightEqZeroOfLt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_intWeight_nonneg_546dc8b33f2f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_int_partial_le_78baa4e70c2b

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
open Elem
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace IntegerLogSquareTail
theorem _root_.solution : IntegerLogSquareTail.Statement := by
  intro f N B₀ hf hN hB
  have hB16 : 16 ≤ B₀ := by
    have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
    have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  set s : Set ℕ := {m | B₀ < m}
  have hind : s.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ 2) = intWeight B₀ := by
    funext m
    by_cases h : B₀ < m
    · simp [s, Set.indicator_of_mem, h, intWeight]
    · simp [s, Set.indicator_of_notMem, h, intWeight]
  have hsum : Summable (intWeight B₀) :=
    summable_of_sum_range_le (intWeight_nonneg B₀) (int_partial_le B₀ hB16)
  have hsub : Summable (fun m : s => Real.log m / (m : ℝ) ^ 2) := by
    have := (summable_subtype_iff_indicator (f := fun m : ℕ => Real.log m / (m : ℝ) ^ 2)
      (s := s)).mpr (by rw [hind]; exact hsum)
    exact this
  refine ⟨hsub, ?_⟩
  have : ∑' m : s, Real.log m / (m : ℝ) ^ 2 ≤ 2 * (1 + Real.log B₀) / B₀ := by
    rw [tsum_subtype s (fun m : ℕ => Real.log m / (m : ℝ) ^ 2), hind]
    exact Real.tsum_le_of_sum_range_le (intWeight_nonneg B₀) (int_partial_le B₀ hB16)
  exact this
end IntegerLogSquareTail
end GroundTheory.Heights₂.Heights.RestTerms

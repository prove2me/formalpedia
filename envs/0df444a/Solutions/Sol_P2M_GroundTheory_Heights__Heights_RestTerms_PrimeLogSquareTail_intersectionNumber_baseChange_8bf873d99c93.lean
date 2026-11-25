-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_PrimeLogSquareTail_intersectionNumber_baseChange_8bf873d99c93
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:44:22.521732+00:00
-- url     : https://prove2.me/submissions/c356b05c-67f6-411e-a73a-9b448a80c669

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PrimeWeightEqZeroOfLt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_primeWeight_nonneg_6255b916e79a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_prime_partial_le_66a4bd05bbf2

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
namespace PrimeLogSquareTail
theorem _root_.solution : PrimeLogSquareTail.Statement := by
  intro B hB
  set s : Set ℕ := {p | p.Prime ∧ B < p}
  have hind : s.indicator (fun p : ℕ => Real.log p / (p : ℝ) ^ 2) =
      fun i => primeWeight B i / (i : ℝ) ^ 2 := by
    funext i
    by_cases h : i.Prime ∧ B < i
    · simp [s, Set.indicator_of_mem, h, primeWeight]
    · simp [s, Set.indicator_of_notMem, h, primeWeight]
  have hnn : ∀ i, 0 ≤ primeWeight B i / (i : ℝ) ^ 2 := fun i =>
    div_nonneg (primeWeight_nonneg B i) (by positivity)
  have hsum : Summable (fun i => primeWeight B i / (i : ℝ) ^ 2) :=
    summable_of_sum_range_le hnn (prime_partial_le B hB)
  have hsub : Summable (fun p : s => Real.log p / (p : ℝ) ^ 2) := by
    have := (summable_subtype_iff_indicator (f := fun p : ℕ => Real.log p / (p : ℝ) ^ 2)
      (s := s)).mpr (by rw [hind]; exact hsum)
    exact this
  refine ⟨hsub, ?_⟩
  have : ∑' p : s, Real.log p / (p : ℝ) ^ 2 ≤ 2 * Real.log 4 / B := by
    rw [tsum_subtype s (fun p : ℕ => Real.log p / (p : ℝ) ^ 2), hind]
    exact Real.tsum_le_of_sum_range_le hnn (prime_partial_le B hB)
  exact this
end PrimeLogSquareTail
end GroundTheory.Heights₂.Heights.RestTerms

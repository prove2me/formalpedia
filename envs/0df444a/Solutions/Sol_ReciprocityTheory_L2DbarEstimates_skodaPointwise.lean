-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.skodaPointwise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:30:53.233818+00:00
-- url     : https://prove2.me/submissions/8f2a6b92-6ea7-461a-bb24-afab07366bd2

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_sqNorm_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_trace_mul_transpose
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_skodaMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {p : ℕ}
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution : SkodaPointwiseStatement := by
  intro p n g J V hg
  have hs := sqNorm_pos hg
  have hM := skodaMatrix p n g J V hg
  have hsum : (∑ i, ∑ k, (starRingEnd ℂ ((projPerp g * J) i k) / ((sqNorm g : ℝ) : ℂ)) *
      starRingEnd ℂ (V i k)) =
      starRingEnd ℂ (trace (projPerp g * J * Vᵀ)) / ((sqNorm g : ℝ) : ℂ) := by
    rw [trace_mul_transpose, map_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    ring
  rw [hsum, Complex.normSq_div, Complex.normSq_conj, Complex.normSq_ofReal]
  calc sqNorm g * (Complex.normSq (trace (projPerp g * J * Vᵀ)) / (sqNorm g * sqNorm g))
      = Complex.normSq (trace (projPerp g * J * Vᵀ)) / sqNorm g := by
        rw [mul_div_assoc', mul_div_mul_left _ _ hs.ne']
    _ ≤ ((p : ℝ) - 1) * (∑ i, sqNorm ((projPerp g * J) *ᵥ V i)) / sqNorm g :=
        div_le_div_of_nonneg_right hM hs.le
    _ = _ := by rw [mul_div_assoc, Finset.sum_div]
end ReciprocityTheory.L2DbarEstimates

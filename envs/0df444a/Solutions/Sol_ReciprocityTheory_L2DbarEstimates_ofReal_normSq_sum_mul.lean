-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.ofReal_normSq_sum_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:46.332313+00:00
-- url     : https://prove2.me/submissions/d45194a2-f56d-4b51-a15a-ebd4cebb15b6

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution (a ξ : Fin n → ℂ) :
    ((Complex.normSq (∑ j, a j * ξ j) : ℝ) : ℂ) =
      ∑ j, ∑ kk, a j * conj (a kk) * ξ j * conj (ξ kk) := by
  rw [← mul_conj, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun kk _ => ?_
  rw [map_mul]; ring
end ReciprocityTheory.L2DbarEstimates

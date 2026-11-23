-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.star_dotProduct_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:10.881068+00:00
-- url     : https://prove2.me/submissions/8df2377b-1c63-4554-b3ab-d8b39998e991

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix

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
theorem _root_.solution (g : Fin p → ℂ) : star g ⬝ᵥ g = ((sqNorm g : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, sqNorm, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl
end ReciprocityTheory.L2DbarEstimates

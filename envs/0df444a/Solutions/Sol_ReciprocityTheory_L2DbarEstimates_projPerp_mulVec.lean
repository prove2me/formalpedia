-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.projPerp_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:24.477796+00:00
-- url     : https://prove2.me/submissions/79658851-2660-48ab-a417-e255cdc6e680

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_projPerp_apply

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
theorem _root_.solution (g w : Fin p → ℂ) :
    projPerp g *ᵥ w = w - (((sqNorm g : ℝ) : ℂ)⁻¹ * (star g ⬝ᵥ w)) • g := by
  ext i
  rw [mulVec, dotProduct]
  simp only [projPerp_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    dotProduct, Pi.star_apply]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Complex.star_def]
  ring
end ReciprocityTheory.L2DbarEstimates

-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.evl_dDot_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:35:29.090601+00:00
-- url     : https://prove2.me/submissions/ac8e2814-6ac7-4347-bb70-a002e27c1465

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EvLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open scoped ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℂ)
    (hf : Ck n z 1 f) (hg : Ck n z 1 g) (x : M) (ξ : Fin n → ℂ) :
    dDot n z (fun y => f y * g y) x ξ = dDot n z f x ξ * g x + f x * dDot n z g x ξ := by
  unfold dDot
  simp only [d_mul n z f g hf hg, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun j _ => by ring
end ReciprocityTheory.L2DbarEstimates.I

-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.evl_dDot_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:55:08.647852+00:00
-- url     : https://prove2.me/submissions/9bc97283-03ff-4d7e-97b9-c1bd317196af

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EvLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_const_mul


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
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (c : ℂ)
    (f : M → ℂ) (hf : Ck n z 1 f) (x : M) (ξ : Fin n → ℂ) :
    dDot n z (fun y => c * f y) x ξ = c * dDot n z f x ξ := by
  unfold dDot
  simp only [d_const_mul n z c f hf, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring
end ReciprocityTheory.L2DbarEstimates.I

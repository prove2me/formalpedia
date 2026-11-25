-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.evl_dDot_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:55:04.849008+00:00
-- url     : https://prove2.me/submissions/75ecf9de-4fe9-4b53-8cee-5b89ce6f69b5

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EvLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_add


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
    dDot n z (fun y => f y + g y) x ξ = dDot n z f x ξ + dDot n z g x ξ := by
  unfold dDot
  simp only [d_add n z f g hf hg, add_mul, Finset.sum_add_distrib]
end ReciprocityTheory.L2DbarEstimates.I

-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.evl_dDot_expNeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:18:23.435541+00:00
-- url     : https://prove2.me/submissions/77212eee-52f4-4a1a-b9e2-da5d1e43b06d

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EvLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_deriv_exp_neg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_contDiff_exp_neg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_ckR
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_comp_real


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
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ)
    (hph : SmoothR n z ph) (x : M) (ξ : Fin n → ℂ) :
    dDot n z (fun y => ((Real.exp (-ph y) : ℝ) : ℂ)) x ξ =
      -((Real.exp (-ph x) : ℝ) : ℂ) * dDot n z (fun y => (ph y : ℂ)) x ξ := by
  have h : ∀ j, d n z j (fun y => ((Real.exp (-ph y) : ℝ) : ℂ)) x =
      -((Real.exp (-ph x) : ℝ) : ℂ) * d n z j (fun y => (ph y : ℂ)) x := by
    intro j
    have := d_comp_real n z (fun t => Real.exp (-t)) contDiff_exp_neg ph (SmoothR.ckR n z 1 ph hph) j x
    rw [deriv_exp_neg] at this
    simpa using this
  unfold dDot
  simp only [h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring
end ReciprocityTheory.L2DbarEstimates.I

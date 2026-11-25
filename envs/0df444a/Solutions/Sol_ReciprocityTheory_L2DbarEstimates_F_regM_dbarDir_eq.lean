-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.regM_dbarDir_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:17:24.239162+00:00
-- url     : https://prove2.me/submissions/aa84560a-17cb-4511-a249-5d4338c35ba9

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegGlue
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_HormanderEstimate_RegMDbEqZeroOfNotMem
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {n : ℕ} (g : V n → ℂ) (y v : V n) :
    C.dbarDir g y v = -2 * Complex.I * ∑ j, conj (v j) * wdb n j g y := by
  set L := fderiv ℝ g y with hL
  have hsm : ∀ (c : ℂ) (w : V n), L (c • w) = c.re • L w + c.im • L (Complex.I • w) := by
    intro c w
    have hc : c • w = c.re • w + c.im • (Complex.I • w) := by
      conv_lhs => rw [← Complex.re_add_im c]
      rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
    rw [hc, map_add, map_smul, map_smul]
  have hv : v = ∑ j, v j • bas n j := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr v]
    simp [bas]
  have hIv : Complex.I • v = ∑ j, (Complex.I * v j) • bas n j := by
    conv_lhs => rw [hv]
    simp [Finset.smul_sum, smul_smul]
  have hLv : L v = ∑ j, L (v j • bas n j) := by
    conv_lhs => rw [hv]
    rw [map_sum]
  have hLIv : L (Complex.I • v) = ∑ j, L ((Complex.I * v j) • bas n j) := by
    rw [hIv, map_sum]
  simp only [C.dbarDir, wdb, ← hL]
  rw [hLIv, hLv, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsm (Complex.I * v j) (bas n j), hsm (v j) (bas n j)]
  have hcj : conj (v j) = ((v j).re : ℂ) - ((v j).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hcj]
  simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_sub, sub_zero, zero_add, Complex.ofReal_neg]
  linear_combination (((v j).re : ℂ) * L (Complex.I • bas n j) - ((v j).im : ℂ) * L (bas n j) -
    Complex.I * ((v j).im : ℂ) * L (Complex.I • bas n j)) * Complex.I_sq
end ReciprocityTheory.L2DbarEstimates.F

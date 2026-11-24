-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.intw_fou
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:15.668322+00:00
-- url     : https://prove2.me/submissions/f471b3ba-bb5d-48c1-a76f-b40b9cbdfd63

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
import Theorems.Thm_PositivityTheory_ThKR_LL_fou_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l]
namespace PositivityTheory.ThKR.LL
theorem _root_.solution (p q : Eu l) : Intw (fou l) p q (-q) p := fun f g h => by
  funext x
  simp only [fou_apply, fourier_coe, rf, h, Real.fourier_eq', smul_eq_mul]
  rw [← integral_const_mul, ← integral_add_right_eq_self (μ := volume) (fun v => exp (((2 * π * ⟪p, x⟫ + π * ⟪-q, p⟫ : ℝ) : ℂ) * I) *
    (exp (((-2 * π * ⟪v, x + -q⟫ : ℝ) : ℂ) * I) * f v)) p]
  refine integral_congr_ae (.of_forall fun v => ?_)
  simp only [← mul_assoc, ← Complex.exp_add]
  congr 2
  rw [← add_mul, ← add_mul, ← ofReal_add, ← ofReal_add]
  congr 2
  simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right, real_inner_comm q p, real_inner_comm q v]
  ring
end PositivityTheory.ThKR.LL

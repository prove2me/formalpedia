-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspQCoefficient_analyticAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:47:37.324414+00:00
-- url     : https://prove2.me/submissions/4f2382b6-d08e-461e-b3b2-54d79679566d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspWidths
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferentialCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspQDifferential
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_width_positive


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) : AnalyticAt ℂ (lpsOriginalCuspQCoefficient N f ρ) 0 := by
  have hm := lpsOriginalCuspGroup_width_positive N ρ
  have hp := Subgroup.strictWidthInfty_mem_strictPeriods (lpsOriginalCuspGroup N ρ)
  have ha := ModularFormClass.analyticAt_cuspFunction_zero
    (CuspForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ ρ)) hm hp
  obtain ⟨P,hP⟩ := ha
  have hd : AnalyticAt ℂ
    (dslope (UpperHalfPlane.cuspFunction (lpsOriginalCuspGroup N ρ).strictWidthInfty
      ((f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ)) 0) 0 :=
    ⟨P.fslope,hP.has_fpower_series_dslope_fslope⟩
  exact analyticAt_const.mul hd
end QEC.Coding.TannerLiftedProduct

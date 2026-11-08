-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspTranslateQDifferentialCoefficient_analyticAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:04:16.319625+00:00
-- url     : https://prove2.me/submissions/a4dab37a-6da2-4370-bb33-0519cf24d4e6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.DSlope
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferentialCharts
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0Translate_integerPeriod


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) :
    AnalyticAt ℂ (lpsCuspTranslateQDifferentialCoefficient N f ρ) 0 := by
  have hm : (0:ℝ)<N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have ha := ModularFormClass.analyticAt_cuspFunction_zero
    (CuspForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ ρ)) hm
    (lpsGamma0Translate_integerPeriod N ρ)
  obtain ⟨P,hP⟩ := ha
  have hd : AnalyticAt ℂ
    (dslope (UpperHalfPlane.cuspFunction (N:ℝ)
      ((f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ)) 0) 0 :=
    ⟨P.fslope,hP.has_fpower_series_dslope_fslope⟩
  exact analyticAt_const.mul hd
end QEC.Coding.TannerLiftedProduct

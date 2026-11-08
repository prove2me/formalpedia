-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspTranslateQDifferentialCoefficient_pullback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:04:34.926199+00:00
-- url     : https://prove2.me/submissions/bf30fdd0-7fcb-404a-a1f2-0762f09b3655

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.DSlope
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferentialCharts
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspTranslateQDifferentialCoefficient_qParam
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQParam_deriv

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) (τ : ℍ) (v : ℂ) :
    lpsCuspTranslateQDifferentialCoefficient N f ρ (Function.Periodic.qParam (N:ℝ) τ) *
      (deriv (Function.Periodic.qParam (N:ℝ)) τ*v) =
      (((f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ) τ)*v := by
  rw [lpsCuspTranslateQDifferentialCoefficient_qParam,lpsQParam_deriv]
  have hq := Function.Periodic.qParam_ne_zero (h:=(N:ℝ)) (τ:ℂ)
  have hN : (N:ℂ)≠0 := by exact_mod_cast NeZero.ne N
  push_cast
  field_simp [Complex.two_pi_I_ne_zero,hq,hN]
end QEC.Coding.TannerLiftedProduct

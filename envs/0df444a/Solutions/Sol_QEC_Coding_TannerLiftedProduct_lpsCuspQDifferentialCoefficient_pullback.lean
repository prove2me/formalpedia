-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspQDifferentialCoefficient_pullback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:04:17.831428+00:00
-- url     : https://prove2.me/submissions/d2cf3563-1a6d-4dd0-9c49-6bcfaf2c7610

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.DSlope
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferentialCharts
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspQDifferentialCoefficient_qParam
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQParam_deriv
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspDifferential_apply


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (v : ℂ) :
    lpsCuspQDifferentialCoefficient N f (Function.Periodic.qParam 1 τ) *
      (deriv (Function.Periodic.qParam 1) τ*v) = lpsCuspDifferential N f τ v := by
  rw [lpsCuspQDifferentialCoefficient_qParam,lpsQParam_deriv,lpsCuspDifferential_apply]
  have hq := Function.Periodic.qParam_ne_zero (h:=1) (τ:ℂ)
  norm_num only [Complex.ofReal_one,div_one]
  field_simp [Complex.two_pi_I_ne_zero,hq]
end QEC.Coding.TannerLiftedProduct

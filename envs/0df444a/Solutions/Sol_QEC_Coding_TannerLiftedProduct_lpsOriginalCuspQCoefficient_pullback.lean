-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspQCoefficient_pullback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:50:34.958447+00:00
-- url     : https://prove2.me/submissions/69157a13-a1e1-4dbd-a06a-e1cc854475d1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspWidths
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferentialCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspQDifferential
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspQCoefficient_qParam
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_width_positive
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQParam_deriv


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) (τ : ℍ) (v : ℂ) :
    lpsOriginalCuspQCoefficient N f ρ
      (Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty τ) *
      (deriv (Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty) τ*v) =
      (((f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ) τ)*v := by
  rw [lpsOriginalCuspQCoefficient_qParam,lpsQParam_deriv]
  have hq := Function.Periodic.qParam_ne_zero
    (h:=(lpsOriginalCuspGroup N ρ).strictWidthInfty) (τ:ℂ)
  have hw : ((lpsOriginalCuspGroup N ρ).strictWidthInfty:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (lpsOriginalCuspGroup_width_positive N ρ).ne'
  field_simp [Complex.two_pi_I_ne_zero,hq,hw]
end QEC.Coding.TannerLiftedProduct

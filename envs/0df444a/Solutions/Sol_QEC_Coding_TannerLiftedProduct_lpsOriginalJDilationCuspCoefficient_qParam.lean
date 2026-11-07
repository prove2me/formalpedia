-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJDilationCuspCoefficient_qParam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:46:42.964527+00:00
-- url     : https://prove2.me/submissions/c4827234-73da-499b-8215-07a4f1382262

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilation_cusp_period
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilationCusp_ratio
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_width_positive


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (hN : 0<N) (ρ : SL(2,ℤ)) (τ : ℍ) :
    lpsOriginalJDilationCuspCoefficient N hN ρ
      (Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty (τ:ℂ))=
      lpsOriginalJDilated N hN (Matrix.SpecialLinearGroup.mapGL ℝ ρ•τ) := by
  have hp := lpsOriginalJDilation_cusp_period N hN ρ
  have hw := (lpsOriginalCuspGroup_width_positive N ρ).ne'
  rw [lpsOriginalJDilationCuspCoefficient,
    UpperHalfPlane.eq_cuspFunction τ hw
      (SlashInvariantFormClass.periodic_comp_ofComplex (lpsOriginalJDilationCuspE4 N hN ρ) hp),
    UpperHalfPlane.eq_cuspFunction τ hw
      (SlashInvariantFormClass.periodic_comp_ofComplex (lpsOriginalJDilationCuspDelta N hN ρ) hp)]
  exact lpsOriginalJDilationCusp_ratio N hN ρ τ
end QEC.Coding.TannerLiftedProduct

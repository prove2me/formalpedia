-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJDilation_cusp_period
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:39:53.379104+00:00
-- url     : https://prove2.me/submissions/64fd9d49-0bab-4c87-b2aa-64bfd781636d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilation_cusp_le_translated_SL

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 0<N) (ρ : SL(2,ℤ)) :
    (lpsOriginalCuspGroup N ρ).strictWidthInfty ∈
      (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ ρ)⁻¹ •
        (ConjAct.toConjAct (lpsE2AffineMatrix N hN 0)⁻¹ •
          (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)))).strictPeriods := by
  apply Subgroup.mem_strictPeriods_iff.mpr
  apply lpsOriginalJDilation_cusp_le_translated_SL N hN ρ
  exact Subgroup.mem_strictPeriods_iff.mp
    (Subgroup.strictWidthInfty_mem_strictPeriods (lpsOriginalCuspGroup N ρ))
end QEC.Coding.TannerLiftedProduct

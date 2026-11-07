-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJDilation_cusp_le_translated_SL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:36:53.973652+00:00
-- url     : https://prove2.me/submissions/7cbff9a6-b8c8-4f2a-91c2-9503ff01c203

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilation_Gamma0_le_translated_SL

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : 0<N) (ρ : SL(2,ℤ)) :
    lpsOriginalCuspGroup N ρ ≤
      ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ ρ)⁻¹ •
        (ConjAct.toConjAct (lpsE2AffineMatrix N hN 0)⁻¹ •
          (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))) := by
  exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr
    (lpsOriginalJDilation_Gamma0_le_translated_SL N hN)
end QEC.Coding.TannerLiftedProduct

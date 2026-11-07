-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranchHolomorphic_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:56:20.354704+00:00
-- url     : https://prove2.me/submissions/b0c1acd7-e4ef-47f1-9571-d585c1e82010

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegralSLAction_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeBranchSL_function

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) [Fact p.Prime]
    (i : Option (Fin p)) (τ : ℍ) :
    (lpsOriginalPrimeBranchHolomorphic p i).val τ=lpsOriginalPrimeBranch p i τ := by
  change lpsOriginalJDilated p (Fact.out : p.Prime).pos
    ((Matrix.SpecialLinearGroup.mapGL ℝ (lpsOriginalPrimeBranchSL p i)⁻¹)⁻¹ • τ)=_
  rw [← map_inv,inv_inv,← lpsOriginalIntegralSLAction_eq]
  exact lpsOriginalPrimeBranchSL_function p i τ
end QEC.Coding.TannerLiftedProduct

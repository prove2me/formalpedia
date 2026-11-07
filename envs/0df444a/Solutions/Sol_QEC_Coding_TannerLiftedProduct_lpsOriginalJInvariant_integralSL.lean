-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJInvariant_integralSL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:27:25.543501+00:00
-- url     : https://prove2.me/submissions/f2f9be7d-3257-47c3-995d-623dc719b075

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegralSLAction_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (g : SL(2,ℤ)) (τ : ℍ) :
    lpsOriginalJInvariant (g • τ)=lpsOriginalJInvariant τ := by
  rw [lpsOriginalIntegralSLAction_eq]
  exact lpsOriginalJInvariant_SL_invariant _ ⟨g,rfl⟩ τ
end QEC.Coding.TannerLiftedProduct

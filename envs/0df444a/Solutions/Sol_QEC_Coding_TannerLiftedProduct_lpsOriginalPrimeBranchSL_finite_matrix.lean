-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranchSL_finite_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:26:10.886814+00:00
-- url     : https://prove2.me/submissions/9602ff8d-dbeb-4fb6-ae3b-1ae77da9a272

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) (m : Fin p) :
    (lpsOriginalPrimeBranchSL p (some m) : Matrix (Fin 2) (Fin 2) ℤ)=
      !![0,-1;1,(m.val:ℤ)] := rfl
end QEC.Coding.TannerLiftedProduct

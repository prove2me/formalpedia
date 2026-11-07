-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2AffineMatrix_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:00:53.101022+00:00
-- url     : https://prove2.me/submissions/9e4221af-2cf7-4630-8c42-e8e8ea08a473

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (m : ℕ) (hm : 0<m) (r : ℝ) :
    (lpsE2AffineMatrix m hm r:Matrix (Fin 2) (Fin 2) ℝ)=!![(m:ℝ),r;0,1] := rfl
end QEC.Coding.TannerLiftedProduct

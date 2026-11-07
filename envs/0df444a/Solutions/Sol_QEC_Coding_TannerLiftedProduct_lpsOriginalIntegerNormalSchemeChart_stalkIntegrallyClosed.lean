-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalSchemeChart_stalkIntegrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:00:49.518775+00:00
-- url     : https://prove2.me/submissions/7605587a-e55d-4eed-b8f0-9a464e742248

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.AlgebraicGeometry.FunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalAffineStalk_integrallyClosed
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalAffine_integrallyClosed
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerReciprocalNormalAffine_integrallyClosed


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0<N) (b : Bool)
    (y : lpsOriginalIntegerNormalSchemeChart N hN b) :
    IsIntegrallyClosed ((lpsOriginalIntegerNormalSchemeChart N hN b).presheaf.stalk y) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  cases b with
  | false =>
      let := lpsOriginalIntegerBaseFractionMap.toAlgebra
      let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
      let := lpsOriginalIntegerNormalAffine_integrallyClosed N hN
      exact lpsOriginalNormalAffineStalk_integrallyClosed
        (.of (lpsOriginalIntegerNormalZeroChart N hN)) y
  | true =>
      let := lpsOriginalIntegerReciprocalBaseFractionMap.toAlgebra
      let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
      let := lpsOriginalIntegerReciprocalNormalAffine_integrallyClosed N hN
      exact lpsOriginalNormalAffineStalk_integrallyClosed
        (.of (lpsOriginalIntegerNormalInfinityChart N hN)) y
end QEC.Coding.TannerLiftedProduct

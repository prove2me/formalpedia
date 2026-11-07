-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalSchemeChart_locallyNoetherian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:53:13.060194+00:00
-- url     : https://prove2.me/submissions/c0861b9c-1a6c-4a91-ab6f-26ca7f8d79ca

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalAffine_noetherian
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerReciprocalNormalAffine_noetherian


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0<N) (b : Bool) :
    IsLocallyNoetherian (lpsOriginalIntegerNormalSchemeChart N hN b) := by
  cases b with
  | false =>
      let := lpsOriginalJFractionEmbeddingQ.toAlgebra
      let := lpsOriginalIntegerBaseFractionMap.toAlgebra
      let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
      let := lpsOriginalIntegerNormalAffine_noetherian N hN
      change IsLocallyNoetherian (Spec (.of (lpsOriginalIntegerNormalZeroChart N hN)))
      infer_instance
  | true =>
      let := lpsOriginalJFractionEmbeddingQ.toAlgebra
      let := lpsOriginalIntegerReciprocalBaseFractionMap.toAlgebra
      let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
      let := lpsOriginalIntegerReciprocalNormalAffine_noetherian N hN
      change IsLocallyNoetherian (Spec (.of (lpsOriginalIntegerNormalInfinityChart N hN)))
      infer_instance
end QEC.Coding.TannerLiftedProduct

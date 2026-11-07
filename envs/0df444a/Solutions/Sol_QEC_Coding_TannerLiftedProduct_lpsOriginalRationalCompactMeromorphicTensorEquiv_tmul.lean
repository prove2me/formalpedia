-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRationalCompactMeromorphicTensorEquiv_tmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:15:23.513702+00:00
-- url     : https://prove2.me/submissions/675dcdb6-2d8f-4843-bbc1-ab35d027e6f2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalArithmeticFunctionFieldComparison

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6e81b77173_97
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6e81b77173_99
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6e81b77173_101
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6e81b77173_103
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
    (r : FractionRing (Polynomial ℂ)) (x : lpsOriginalGeneratedFunctionFieldQ N hpos) :
    letI := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
    lpsOriginalRationalCompactMeromorphicTensorEquiv N hpos hN
      (r ⊗ₜ[FractionRing (Polynomial ℚ)] x) =
        r • lpsOriginalGeneratedCompactMeromorphicAlgEquiv N hpos hN
          (lpsOriginalGeneratedQToComplex N hpos x) := by
  let := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
  change lpsOriginalGeneratedCompactMeromorphicAlgEquiv N hpos hN
    (lpsOriginalRationalComplexTensorMap N hpos
      (r ⊗ₜ[FractionRing (Polynomial ℚ)] x)) = _
  rw [lpsOriginalRationalComplexTensorMap_tmul,map_smul]
end QEC.Coding.TannerLiftedProduct

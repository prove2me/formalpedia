-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCompactMeromorphic_generated_representation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:18:25.957095+00:00
-- url     : https://prove2.me/submissions/f4cb4c47-7ca2-4081-94c2-fb8dd1986b6d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    ∃ x : lpsOriginalGeneratedFunctionField N hpos,
      (lpsOriginalGeneratedCompactMeromorphicEquiv N hpos hN x).val =
        (F : Filter.Germ (Filter.codiscrete (LPSOriginalFilledCurve N)) ℂ) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalJFractionEmbedding.toAlgebra
  let y := (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict
    (⟨F,hF⟩ : LPSOriginalFilledMeromorphicFunctionRing N hN)
  refine ⟨(lpsOriginalGeneratedCompactMeromorphicEquiv N hpos hN).symm y,?_⟩
  rw [RingEquiv.apply_symm_apply]
  rfl
end QEC.Coding.TannerLiftedProduct

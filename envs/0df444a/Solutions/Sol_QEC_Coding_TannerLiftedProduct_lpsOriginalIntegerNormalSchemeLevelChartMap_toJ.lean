-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalSchemeLevelChartMap_toJ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:57:12.791065+00:00
-- url     : https://prove2.me/submissions/e4fd109e-9e4a-4156-99b0-119341579476

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) (b : Bool) :
    lpsOriginalIntegerNormalSchemeLevelChartMap N M hNM h4N hN hM b ≫
      lpsOriginalIntegerNormalChartToProjectiveJ N hN b =
    lpsOriginalIntegerNormalChartToProjectiveJ M hM b := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  cases b
  · let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalIntegerBaseToGeneratedField M hM).toAlgebra
    have he : CommRingCat.ofHom (algebraMap (Polynomial ℤ)
        (lpsOriginalIntegerNormalZeroChart N hN)) ≫
        CommRingCat.ofHom (lpsOriginalIntegerNormalZeroLevelPullback N M hNM h4N hN hM) =
        CommRingCat.ofHom (algebraMap (Polynomial ℤ)
          (lpsOriginalIntegerNormalZeroChart M hM)) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro P
      apply Subtype.ext
      apply Subtype.ext
      rfl
    change Spec.map (CommRingCat.ofHom
        (lpsOriginalIntegerNormalZeroLevelPullback N M hNM h4N hN hM)) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℤ)
        (lpsOriginalIntegerNormalZeroChart N hN))) ≫
        lpsOriginalIntegerProjectiveJChartMap false) =
      Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℤ)
        (lpsOriginalIntegerNormalZeroChart M hM))) ≫
        lpsOriginalIntegerProjectiveJChartMap false
    rw [← Category.assoc, ← Spec.map_comp, he]
  · let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalIntegerReciprocalBaseToGeneratedField M hM).toAlgebra
    have he : CommRingCat.ofHom (algebraMap (Polynomial ℤ)
        (lpsOriginalIntegerNormalInfinityChart N hN)) ≫
        CommRingCat.ofHom (lpsOriginalIntegerNormalInfinityLevelPullback N M hNM h4N hN hM) =
        CommRingCat.ofHom (algebraMap (Polynomial ℤ)
          (lpsOriginalIntegerNormalInfinityChart M hM)) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro P
      apply Subtype.ext
      apply Subtype.ext
      rfl
    change Spec.map (CommRingCat.ofHom
        (lpsOriginalIntegerNormalInfinityLevelPullback N M hNM h4N hN hM)) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℤ)
        (lpsOriginalIntegerNormalInfinityChart N hN))) ≫
        lpsOriginalIntegerProjectiveJChartMap true) =
      Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℤ)
        (lpsOriginalIntegerNormalInfinityChart M hM))) ≫
        lpsOriginalIntegerProjectiveJChartMap true
    rw [← Category.assoc, ← Spec.map_comp, he]
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalLevelFunctionFieldPullback_naturality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:35:30.886442+00:00
-- url     : https://prove2.me/submissions/a19d9b13-5b67-4aca-a9a2-fa65b3fd628e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGeneratedFieldPoint_level
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedFunctionFieldEquiv_fieldPoint
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalLevelFunctionFieldPullback_fromSpec

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    (lpsOriginalIntegerNormalGluedFunctionFieldEquiv M hM).toRingHom.comp
      (lpsOriginalIntegerNormalLevelFunctionFieldPullback N M hNM h4N hN hM) =
    (lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom.comp
      (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hN).toRingHom := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_integral M hM
  have hc : CommRingCat.ofHom
      ((lpsOriginalIntegerNormalGluedFunctionFieldEquiv M hM).toRingHom.comp
        (lpsOriginalIntegerNormalLevelFunctionFieldPullback N M hNM h4N hN hM)) =
    CommRingCat.ofHom ((lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom.comp
      (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hN).toRingHom) := by
    apply Spec.map_injective
    rw [← cancel_mono ((lpsOriginalIntegerNormalGluedScheme N hN).fromSpecStalk
      (genericPoint (lpsOriginalIntegerNormalGluedScheme N hN)))]
    change Spec.map (CommRingCat.ofHom
      (lpsOriginalIntegerNormalLevelFunctionFieldPullback N M hNM h4N hN hM) ≫
        CommRingCat.ofHom (lpsOriginalIntegerNormalGluedFunctionFieldEquiv M hM).toRingHom) ≫ _ =
      Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hN).toRingHom ≫
        CommRingCat.ofHom (lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom) ≫ _
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      lpsOriginalIntegerNormalLevelFunctionFieldPullback_fromSpec,
      lpsOriginalIntegerNormalGluedFunctionFieldEquiv_fieldPoint,
      ← Category.assoc, lpsOriginalIntegerNormalGluedFunctionFieldEquiv_fieldPoint]
    exact (lpsOriginalIntegerNormalGeneratedFieldPoint_level N M hNM h4N hN hM).symm
  exact congrArg CommRingCat.Hom.hom hc
end QEC.Coding.TannerLiftedProduct

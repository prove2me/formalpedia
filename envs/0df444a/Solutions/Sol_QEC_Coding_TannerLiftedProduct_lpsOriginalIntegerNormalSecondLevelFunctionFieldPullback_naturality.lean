-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback_naturality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:02:27.089102+00:00
-- url     : https://prove2.me/submissions/18eae659-20df-4388-8739-76b7574efc45

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGeneratedFieldPoint_secondLevel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback_fromSpec
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedFunctionFieldEquiv_fieldPoint


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    (lpsOriginalIntegerNormalGluedFunctionFieldEquiv M hM).toRingHom.comp
      (lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback N M hNM h4N hN hM) =
    (lpsOriginalRationalFrickeLevelPullback N M hNM h4N hN hM).comp
      (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hN).toRingHom := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_integral M hM
  have hc : CommRingCat.ofHom
      ((lpsOriginalIntegerNormalGluedFunctionFieldEquiv M hM).toRingHom.comp
        (lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback N M hNM h4N hN hM)) =
    CommRingCat.ofHom ((lpsOriginalRationalFrickeLevelPullback N M hNM h4N hN hM).comp
      (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hN).toRingHom) := by
    apply Spec.map_injective
    rw [← cancel_mono ((lpsOriginalIntegerNormalGluedScheme N hN).fromSpecStalk
      (genericPoint (lpsOriginalIntegerNormalGluedScheme N hN)))]
    change Spec.map (CommRingCat.ofHom
      (lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback N M hNM h4N hN hM) ≫
        CommRingCat.ofHom (lpsOriginalIntegerNormalGluedFunctionFieldEquiv M hM).toRingHom) ≫ _ =
      Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hN).toRingHom ≫
        CommRingCat.ofHom (lpsOriginalRationalFrickeLevelPullback N M hNM h4N hN hM)) ≫ _
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback_fromSpec,
      lpsOriginalIntegerNormalGluedFunctionFieldEquiv_fieldPoint,
      ← Category.assoc, lpsOriginalIntegerNormalGluedFunctionFieldEquiv_fieldPoint]
    exact lpsOriginalIntegerNormalGeneratedFieldPoint_secondLevel N M hNM h4N hN hM
  exact congrArg CommRingCat.Hom.hom hc
end QEC.Coding.TannerLiftedProduct

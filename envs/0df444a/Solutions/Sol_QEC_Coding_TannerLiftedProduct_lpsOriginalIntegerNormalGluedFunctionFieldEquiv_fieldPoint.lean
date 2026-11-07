-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedFunctionFieldEquiv_fieldPoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:31:17.440404+00:00
-- url     : https://prove2.me/submissions/525e6865-7481-42d9-815c-f346cfb37f20

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGenericStalkMap_fromSpec
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFractionFieldEquiv_fieldPoint
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalAffine_fractionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedChartMap_openImmersion


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    Spec.map (CommRingCat.ofHom
      (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hN).toRingHom) ≫
      (lpsOriginalIntegerNormalGluedScheme N hN).fromSpecStalk
        (genericPoint (lpsOriginalIntegerNormalGluedScheme N hN)) =
      lpsOriginalIntegerNormalGeneratedFieldPoint N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerBaseFractionMap.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalSchemeChart_integral N hN false
  let := lpsOriginalIntegerNormalGluedChartMap_openImmersion N hN false
  let X := lpsOriginalIntegerNormalGluedScheme N hN
  let R : CommRingCat := .of (lpsOriginalIntegerNormalZeroChart N hN)
  let : IsDomain R := inferInstanceAs (IsDomain (lpsOriginalIntegerNormalZeroChart N hN))
  let i := lpsOriginalIntegerNormalGluedChartMap N hN false
  let η := genericPoint (lpsOriginalIntegerNormalSchemeChart N hN false)
  have hη : i η = genericPoint X := genericPoint_eq_of_isOpenImmersion i
  let e := eqToIso (congrArg X.presheaf.stalk hη.symm) ≪≫ asIso (i.stalkMap η)
  let : IsFractionRing R (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    lpsOriginalIntegerNormalAffine_fractionField N hN
  let : Algebra R (Spec R).functionField := instAlgebraCarrierFunctionFieldSpec R
  let : IsFractionRing R (Spec R).functionField := functionField_isFractionRing_of_affine R
  let d := IsFractionRing.ringEquivOfRingEquiv
    (K := (Spec R).functionField) (L := lpsOriginalGeneratedFunctionFieldQ N hN)
      (RingEquiv.refl R)
  change Spec.map (e.hom ≫ CommRingCat.ofHom d.toRingHom) ≫
    X.fromSpecStalk (genericPoint X) =
      Spec.map (CommRingCat.ofHom (algebraMap R (lpsOriginalGeneratedFunctionFieldQ N hN))) ≫ i
  rw [Spec.map_comp, Category.assoc]
  have he : Spec.map e.hom ≫ X.fromSpecStalk (genericPoint X) =
      (Spec R).fromSpecStalk η ≫ i :=
    lpsOriginalGenericStalkMap_fromSpec i η (genericPoint X) hη
  rw [he, ← Category.assoc]
  exact congrArg (fun g => g ≫ i)
    (lpsOriginalFractionFieldEquiv_fieldPoint R (lpsOriginalGeneratedFunctionFieldQ N hN))
end QEC.Coding.TannerLiftedProduct

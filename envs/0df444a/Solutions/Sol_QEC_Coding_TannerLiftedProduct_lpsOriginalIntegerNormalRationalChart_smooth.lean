-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalRationalChart_smooth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:26:00.173663+00:00
-- url     : https://prove2.me/submissions/934497e6-506b-499c-bf10-fa11a805be06

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_CharZeroCurveSmoothness
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalKaehlerInjective
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGlobalNormalizationComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCharacteristicZeroSmooth
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerZeroChart_rationalSmooth
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerInfinityChart_rationalSmooth
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_NormalizationBaseChange_normalizationTensorSpecIso_constantRingHomProjection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerSpecZ_hom_unique


set_option autoImplicit false
open scoped TensorProduct
open CategoryTheory AlgebraicGeometry
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hpos : 0 < N) (b : Bool) :
    Smooth (pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))
      (lpsOriginalIntegerNormalGluedChartMap N hpos b ≫
        lpsOriginalIntegerNormalGluedToSpecZ N hpos)) := by
  cases b with
  | false =>
    let A := lpsOriginalIntegerNormalZeroChart N hpos
    let : Algebra ℤ A := Ring.toIntAlgebra A
    let : SMul ℤ A := Algebra.toSMul
    let : Module ℤ A := Algebra.toModule
    let : Algebra.Smooth ℚ (ℚ ⊗[ℤ] A) :=
      lpsOriginalIntegerZeroChart_rationalSmooth N hpos
    have hm := lpsOriginalIntegerSpecZ_hom_unique A
      (lpsOriginalIntegerNormalGluedChartMap N hpos false ≫
        lpsOriginalIntegerNormalGluedToSpecZ N hpos)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ A)))
    rw [hm]
    let e := QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.normalizationTensorSpecIso
      (R := ℤ) (S := ℚ) (AlgEquiv.refl (R := ℚ) (A₁ := ℚ ⊗[ℤ] A))
    have he := QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.normalizationTensorSpecIso_constantRingHomProjection
      (R := ℤ) (S := ℚ) (AlgEquiv.refl (R := ℚ) (A₁ := ℚ ⊗[ℤ] A))
    have hs : Smooth (e.hom ≫ pullback.fst _ _) := by
      rw [he]
      apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      change (algebraMap ℚ (ℚ ⊗[ℤ] A)).Smooth
      exact RingHom.smooth_algebraMap.mpr inferInstance
    let : Smooth (e.hom ≫ pullback.fst _ _) := hs
    rw [← e.inv_hom_id_assoc (pullback.fst _ _)]
    infer_instance
  | true =>
    let A := lpsOriginalIntegerNormalInfinityChart N hpos
    let : Algebra ℤ A := Ring.toIntAlgebra A
    let : SMul ℤ A := Algebra.toSMul
    let : Module ℤ A := Algebra.toModule
    let : Algebra.Smooth ℚ (ℚ ⊗[ℤ] A) :=
      lpsOriginalIntegerInfinityChart_rationalSmooth N hpos
    have hm := lpsOriginalIntegerSpecZ_hom_unique A
      (lpsOriginalIntegerNormalGluedChartMap N hpos true ≫
        lpsOriginalIntegerNormalGluedToSpecZ N hpos)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ A)))
    rw [hm]
    let e := QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.normalizationTensorSpecIso
      (R := ℤ) (S := ℚ) (AlgEquiv.refl (R := ℚ) (A₁ := ℚ ⊗[ℤ] A))
    have he := QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.normalizationTensorSpecIso_constantRingHomProjection
      (R := ℤ) (S := ℚ) (AlgEquiv.refl (R := ℚ) (A₁ := ℚ ⊗[ℤ] A))
    have hs : Smooth (e.hom ≫ pullback.fst _ _) := by
      rw [he]
      apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      change (algebraMap ℚ (ℚ ⊗[ℤ] A)).Smooth
      exact RingHom.smooth_algebraMap.mpr inferInstance
    let : Smooth (e.hom ≫ pullback.fst _ _) := hs
    rw [← e.inv_hom_id_assoc (pullback.fst _ _)]
    infer_instance
end QEC.Coding.TannerLiftedProduct

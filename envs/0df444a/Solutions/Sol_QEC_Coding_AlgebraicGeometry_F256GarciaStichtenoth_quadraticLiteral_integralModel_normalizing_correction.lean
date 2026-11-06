-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_integralModel_normalizing_correction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:23:09.865279+00:00
-- url     : https://prove2.me/submissions/946bfb77-9033-4f89-9341-826ca556647b

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_PlaceLocalization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticNormalization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalNormalization
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticLiteral_heightOnePrime_normalizing_correction
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_quadraticArtinSchreierUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_regularQuadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_heightOnePlace_order_eq_of_map_eq
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_quadraticArtinSchreierUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_regularQuadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply



set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (A B C K L : Type*) [CommRing A] [CommRing B] [CommRing C]
    [_root_.Field K] [_root_.Field L]
    [IsDomain A] [IsLocalRing A] [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [Algebra F256 K] [Algebra F256 L]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [Algebra B C] [Algebra C L] [IsFractionRing C L] [IsScalarTower B C L]
    [IsIntegralClosure C B L] [Module.IsTorsionFree B C]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.IsTorsionFree B L]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    [Finite (heightOnePlace (k := F256) (K := K) H).residueField]
    (Q : IsDedekindDomain.HeightOneSpectrum C) [Q.asIdeal.LiesOver H.asIdeal]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤)
    (ha : (heightOnePlace (k := F256) (K := K) H).order a = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) H).order a)
    (b : K)
    (hb : (heightOnePlace (k := F256) (K := K) H).order b = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) H).order b) :
    ∃ c : L,
      (c = 0 ∨ (heightOnePlace (k := F256) (K := L) Q).order c = -1) ∧
      ((heightOnePlace (k := F256) (K := L) Q).order (algebraMap K L b + c ^ 2 + c) = -1 ∨
        0 ≤ (heightOnePlace (k := F256) (K := L) Q).order (algebraMap K L b + c ^ 2 + c)) := by
  let N := integralClosure B L
  letI : IsDedekindDomain N := integralClosure.isDedekindDomain B K L
  letI : IsFractionRing N L := integralClosure.isFractionRing_of_finite_extension K L
  letI : Module.IsTorsionFree B N := IsIntegralClosure.isTorsionFree B L
  let σ : N ≃ₐ[B] C := IsIntegralClosure.equiv B N L C
  let J := IsDedekindDomain.HeightOneSpectrum.comap σ.toRingHom σ.surjective Q
  letI : J.asIdeal.LiesOver H.asIdeal := by
    refine Ideal.LiesOver.mk ?_
    change H.asIdeal = Ideal.comap (algebraMap B N) (Ideal.comap σ.toRingHom Q.asIdeal)
    rw [Ideal.comap_comap]
    rw [show σ.toRingHom.comp (algebraMap B N) = algebraMap B C by
      ext b
      exact σ.commutes b]
    exact (show Q.asIdeal.LiesOver H.asIdeal from inferInstance).over
  obtain ⟨c, hc, hcorrected⟩ := quadraticLiteral_heightOnePrime_normalizing_correction
    A B K L H J a y hy hdegree hgen ha b hb
  letI : Algebra N C := σ.toRingHom.toAlgebra
  letI : IsScalarTower N C L := IsScalarTower.of_algebraMap_eq fun x =>
    (IsIntegralClosure.algebraMap_equiv B N L C x).symm
  letI : FaithfulSMul N C := (faithfulSMul_iff_algebraMap_injective N C).mpr σ.injective
  letI : Q.asIdeal.LiesOver J.asIdeal := ⟨rfl⟩
  have hmap : Ideal.map (algebraMap N C) J.asIdeal = Q.asIdeal :=
    Q.asIdeal.map_comap_of_surjective σ.toRingHom σ.surjective
  have horders (x : L) := heightOnePlace_order_eq_of_map_eq (k := F256) J Q hmap x
  refine ⟨c, ?_, ?_⟩
  · simpa only [horders] using hc
  · simpa only [horders] using hcorrected
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

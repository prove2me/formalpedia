-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticCompositumCell_normalized_weakDifferent_or_redundant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:25:50.891998+00:00
-- url     : https://prove2.me/submissions/e9ffd188-906b-4fa8-8a77-aff5b474014a

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalNormalization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_TrivialFieldExtension
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticCompositumCell
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_literalQuadratic_finrank_eq_one_or_two
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_adjoin_add_algebraMap_eq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_artinSchreier_baseChange_translate_equation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_quadraticArtinSchreierUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_regularQuadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticLiteral_integralModel_normalizing_correction
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticLiteral_integralModel_weakDifferent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_heightOnePlace_order_algebraMap_of_finrank_eq_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ramificationIdx_and_weakDifferent_of_finrank_eq_one
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
variable (A B C D K L E : Type*)
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [_root_.Field K] [_root_.Field L] [_root_.Field E]
    [IsDomain A] [IsLocalRing A]
    [IsDedekindDomain B] [IsDedekindDomain C] [IsDedekindDomain D]
    [Algebra F256 K] [Algebra F256 L] [Algebra F256 E]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [Algebra A C] [Algebra.IsIntegral A C] [Module.IsTorsionFree A C]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [Algebra B C] [Algebra C L] [IsFractionRing C L] [IsScalarTower B C L]
    [IsIntegralClosure C B L] [Module.IsTorsionFree B C]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.IsTorsionFree B L]
    [Algebra K E] [Algebra L E] [IsScalarTower K L E]
    [Algebra C E] [IsScalarTower C L E]
    [Algebra C D] [Algebra D E] [IsScalarTower C D E]
    [IsIntegralClosure D C E] [Module.IsTorsionFree C D]
    [FiniteDimensional L E] [Algebra.IsSeparable L E]
    [Module.IsTorsionFree C E]
include A
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    [IsFractionRing D E]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    [Finite (heightOnePlace (k := F256) (K := K) H).residueField]
    (P : IsDedekindDomain.HeightOneSpectrum C) [P.asIdeal.LiesOver H.asIdeal]
    (Q : IsDedekindDomain.HeightOneSpectrum D) [Q.asIdeal.LiesOver P.asIdeal]
    (a b : K) (y : L) (z : E)
    (hy : y ^ 2 + y = algebraMap K L a)
    (hz : z ^ 2 + z = algebraMap K E b)
    (hgen : K⟮y⟯ = ⊤) (hgenUpper : L⟮z⟯ = ⊤)
    (ha : (heightOnePlace (k := F256) (K := K) H).order a = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) H).order a)
    (hb : (heightOnePlace (k := F256) (K := K) H).order b = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) H).order b) :
    ∃ c : L,
      ((heightOnePlace (k := F256) (K := L) P).order
          (algebraMap K L b + c ^ 2 + c) = -1 ∨
        0 ≤ (heightOnePlace (k := F256) (K := L) P).order
          (algebraMap K L b + c ^ 2 + c)) ∧
      (z + algebraMap L E c) ^ 2 + (z + algebraMap L E c) =
        algebraMap L E (algebraMap K L b + c ^ 2 + c) ∧
      L⟮z + algebraMap L E c⟯ = ⊤ ∧
      multiplicity Q.asIdeal (differentIdeal C D) =
        2 * (P.asIdeal.ramificationIdx' Q.asIdeal - 1) := by
  letI : Module.Finite B C := IsIntegralClosure.finite B K L C
  letI : Module.Finite C D := IsIntegralClosure.finite C L E D
  obtain ⟨c, hc⟩ : ∃ c : L,
      (heightOnePlace (k := F256) (K := L) P).order
          (algebraMap K L b + c ^ 2 + c) = -1 ∨
        0 ≤ (heightOnePlace (k := F256) (K := L) P).order
          (algebraMap K L b + c ^ 2 + c) := by
    rcases literalQuadratic_finrank_eq_one_or_two a y hy hgen with hdeg | hdeg
    · refine ⟨0, ?_⟩
      simpa only [zero_pow (by decide : 2 ≠ 0), add_zero,
        heightOnePlace_order_algebraMap_of_finrank_eq_one B C K L H P hdeg b] using hb
    · obtain ⟨c, _, hc⟩ := quadraticLiteral_integralModel_normalizing_correction
        A B C K L H P a y hy hdeg hgen ha b hb
      exact ⟨c, hc⟩
  have heq := artinSchreier_baseChange_translate_equation b z hz c
  have hgenerates : L⟮z + algebraMap L E c⟯ = ⊤ := by
    rw [adjoin_add_algebraMap_eq, hgenUpper]
  refine ⟨c, hc, heq, hgenerates, ?_⟩
  rcases literalQuadratic_finrank_eq_one_or_two
    (algebraMap K L b + c ^ 2 + c) (z + algebraMap L E c)
    heq hgenerates with hdeg | hdeg
  · exact (ramificationIdx_and_weakDifferent_of_finrank_eq_one
      C D L E P Q hdeg).2
  · exact quadraticLiteral_integralModel_weakDifferent A C D L E P Q
      (algebraMap K L b + c ^ 2 + c) (z + algebraMap L E c)
      heq hdeg hgenerates hc
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticCompositumCell_normalized_weakDifferent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:31:41.704206+00:00
-- url     : https://prove2.me/submissions/924a97eb-8fef-44cc-8899-23fa9aefd7b8

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalNormalization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_TrivialFieldExtension
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticCompositumCell
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_adjoin_add_algebraMap_eq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_artinSchreier_baseChange_translate_equation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticLiteral_integralModel_normalizing_correction
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticLiteral_integralModel_weakDifferent


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
    (H : IsDedekindDomain.HeightOneSpectrum B)
    [Finite (heightOnePlace (k := F256) (K := K) H).residueField]
    (P : IsDedekindDomain.HeightOneSpectrum C) [P.asIdeal.LiesOver H.asIdeal]
    (Q : IsDedekindDomain.HeightOneSpectrum D) [Q.asIdeal.LiesOver P.asIdeal]
    (a b : K) (y : L) (z : E)
    (hy : y ^ 2 + y = algebraMap K L a)
    (hz : z ^ 2 + z = algebraMap K E b)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤)
    (hdegreeUpper : Module.finrank L E = 2) (hgenUpper : L⟮z⟯ = ⊤)
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
  obtain ⟨c, _, hc⟩ := quadraticLiteral_integralModel_normalizing_correction
    A B C K L H P a y hy hdegree hgen ha b hb
  have heq := artinSchreier_baseChange_translate_equation b z hz c
  have hgenerates : L⟮z + algebraMap L E c⟯ = ⊤ := by
    rw [adjoin_add_algebraMap_eq, hgenUpper]
  refine ⟨c, hc, heq, hgenerates, ?_⟩
  exact quadraticLiteral_integralModel_weakDifferent A C D L E P Q
    (algebraMap K L b + c ^ 2 + c) (z + algebraMap L E c)
    heq hdegreeUpper hgenerates hc
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

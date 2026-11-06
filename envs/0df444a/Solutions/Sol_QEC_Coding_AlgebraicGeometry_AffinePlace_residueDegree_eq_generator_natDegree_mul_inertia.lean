-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.AffinePlace.residueDegree_eq_generator_natDegree_mul_inertia
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:44:28.680093+00:00
-- url     : https://prove2.me/submissions/12a77afa-0936-4e43-b39b-59ca4d9e6082

import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectNormCount
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_constantsToResidue_apply


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.AffinePlace
open scoped Polynomial RatFunc nonZeroDivisors
open Submodule.IsPrincipal
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
namespace QEC.Coding.AlgebraicGeometry.AffinePlace
theorem _root_.solution
    (P : carrier k F) :
    residueDegree k F P =
      (generator (basePrime k F P)).natDegree *
        (basePrime k F P).inertiaDeg' P.asIdeal := by
  classical
  let B : Type _ := _root_.FunctionField.ringOfIntegers k F
  let p : Ideal k[X] := basePrime k F P
  letI : Module.Finite k[X] B := finite_ringOfIntegers k F
  letI : Module.IsTorsionFree k[X] F :=
    Module.IsTorsionFree.trans_faithfulSMul k[X] k⟮X⟯ F
  letI : Algebra.IsIntegral k[X] B := IsIntegralClosure.isIntegral_algebra k[X] F
  letI : P.asIdeal.LiesOver p := ⟨rfl⟩
  letI : P.asIdeal.IsMaximal := P.isPrime.isMaximal P.ne_bot
  letI : p.IsMaximal := Ideal.IsMaximal.under k[X] P.asIdeal
  letI : Field (k[X] ⧸ p) := Ideal.Quotient.field p
  letI : Field (B ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  letI : Algebra (k[X] ⧸ p) (B ⧸ P.asIdeal) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.over_def P.asIdeal p).ge
  letI : Algebra (k[X] ⧸ p) (residueField k F P) :=
    ((algebraMap (B ⧸ P.asIdeal) (residueField k F P)).comp
      (algebraMap (k[X] ⧸ p) (B ⧸ P.asIdeal))).toAlgebra
  letI : IsScalarTower (k[X] ⧸ p) (B ⧸ P.asIdeal) (residueField k F P) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra k (residueField k F P) := residueAlgebra k F P
  letI : IsScalarTower k (k[X] ⧸ p) (residueField k F P) :=
    IsScalarTower.of_algebraMap_eq
      (R := k) (S := k[X] ⧸ p) (A := residueField k F P) fun a => by
      change constantsToResidue k F P a = _
      rw [constantsToResidue_apply]
      change algebraMap B (residueField k F P)
          (algebraMap k[X] B (Polynomial.C a)) =
        algebraMap (B ⧸ P.asIdeal) (residueField k F P)
          (Ideal.Quotient.mk P.asIdeal (algebraMap k[X] B (Polynomial.C a)))
      rw [Ideal.algebraMap_quotient_residueField_mk]
  unfold residueDegree
  letI : FiniteDimensional k (residueField k F P) :=
    residueField_finiteDimensional k F P
  rw [← Module.finrank_mul_finrank k (k[X] ⧸ p) (residueField k F P)]
  congr 1
  · rw [← Ideal.span_singleton_generator p]
    exact finrank_quotient_span_eq_natDegree
  · rw [← Module.finrank_mul_finrank (k[X] ⧸ p) (B ⧸ P.asIdeal)
      (residueField k F P),
      Module.finrank_of_bijective_algebraMap
        (Ideal.bijective_algebraMap_quotient_residueField P.asIdeal),
      mul_one,
      ← Ideal.inertiaDeg_algebraMap p P.asIdeal]
end QEC.Coding.AlgebraicGeometry.AffinePlace

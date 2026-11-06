-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepReciprocalRoot_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:45:22.535798+00:00
-- url     : https://prove2.me/submissions/79a59df6-6c3f-42a5-b536-aaa000ac55f7

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_FixedFieldArtinSchreier
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


section
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
private theorem eval2_trinomial {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (y : S) (a b : R) (m n : ℕ) :
    eval₂ f y (X ^ m + C a * X ^ n + C b) =
      y ^ m + f a * y ^ n + f b := by
  rw [eval₂_add, eval₂_add, eval₂_X_pow, eval₂_mul f y,
    eval₂_C, eval₂_X_pow, eval₂_C]
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) : stepReciprocalRoot P x hx ≠ 0 := by
  intro hzero
  have hroot := AdjoinRoot.eval₂_root (stepPolynomial P x hx)
  change AdjoinRoot.root (stepPolynomial P x hx) = 0 at hzero
  rw [hzero] at hroot
  have hpolyEval :
      eval₂ (AdjoinRoot.of (stepPolynomial P x hx)) 0
          (stepPolynomial P x hx) =
        eval₂ (AdjoinRoot.of (stepPolynomial P x hx)) 0
          (X ^ 16 + C (x⁻¹ ^ 16) * X ^ 15 + C x⁻¹) :=
    congrArg (eval₂ (AdjoinRoot.of (stepPolynomial P x hx)) 0)
      (stepPolynomial_eq_explicit P x hx)
  have hexplicit :
      eval₂ (AdjoinRoot.of (stepPolynomial P x hx)) 0
          (X ^ 16 + C (x⁻¹ ^ 16) * X ^ 15 + C x⁻¹) = 0 :=
    hpolyEval.symm.trans hroot
  rw [eval2_trinomial (AdjoinRoot.of (stepPolynomial P x hx)) 0
    (x⁻¹ ^ 16) x⁻¹ 16 15] at hexplicit
  have hmap : AdjoinRoot.of (stepPolynomial P x hx)
      x⁻¹ ≠ 0 := by
    simpa only [map_zero] using
      (AdjoinRoot.of (stepPolynomial P x hx)).injective.ne
        (inv_ne_zero (coordinate_ne_zero P x hx))
  apply hmap
  simpa only [zero_pow (by norm_num : (16 : ℕ) ≠ 0),
    zero_pow (by norm_num : (15 : ℕ) ≠ 0), mul_zero, zero_add, add_zero] using hexplicit
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

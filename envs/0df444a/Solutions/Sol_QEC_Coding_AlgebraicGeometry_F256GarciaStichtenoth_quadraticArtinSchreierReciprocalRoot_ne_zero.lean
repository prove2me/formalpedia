-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierReciprocalRoot_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:48:58.681989+00:00
-- url     : https://prove2.me/submissions/e4cfd91b-b21e-476d-a367-f3f9bc67cbc1

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStep
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
private theorem quadraticArtinSchreier_eval2_quadratic
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (y : S) (c d : R) :
    eval₂ f y (X ^ 2 + C c * X + C d) =
      y ^ 2 + f c * y + f d := by
  rw [eval₂_add, eval₂_add, eval₂_X_pow, eval₂_mul f y,
    eval₂_C, eval₂_X, eval₂_C]
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    quadraticArtinSchreierReciprocalRoot P a ha ≠ 0 := by
  intro hzero
  have hroot := AdjoinRoot.eval₂_root
    (quadraticArtinSchreierPolynomial P a ha)
  change AdjoinRoot.root (quadraticArtinSchreierPolynomial P a ha) = 0 at hzero
  rw [hzero] at hroot
  have hpolyEval := congrArg
    (eval₂ (AdjoinRoot.of (quadraticArtinSchreierPolynomial P a ha)) 0)
    (quadraticArtinSchreierPolynomial_eq_explicit P a ha)
  have hexplicit :
      eval₂ (AdjoinRoot.of (quadraticArtinSchreierPolynomial P a ha)) 0
          (X ^ 2 + C a⁻¹ * X + C a⁻¹) = 0 :=
    hpolyEval.symm.trans hroot
  rw [quadraticArtinSchreier_eval2_quadratic
    (AdjoinRoot.of (quadraticArtinSchreierPolynomial P a ha)) 0
      a⁻¹ a⁻¹] at hexplicit
  have hmap :
      AdjoinRoot.of (quadraticArtinSchreierPolynomial P a ha) a⁻¹ ≠ 0 := by
    simpa only [map_zero] using
      (AdjoinRoot.of
        (quadraticArtinSchreierPolynomial P a ha)).injective.ne
          (inv_ne_zero (quadraticArtinSchreier_parameter_ne_zero P a ha))
  apply hmap
  simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_pow (by norm_num : (1 : ℕ) ≠ 0), mul_zero, zero_add,
    add_zero] using hexplicit
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

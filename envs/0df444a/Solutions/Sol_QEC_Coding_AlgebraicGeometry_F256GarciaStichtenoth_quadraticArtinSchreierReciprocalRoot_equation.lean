-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierReciprocalRoot_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:49:00.982863+00:00
-- url     : https://prove2.me/submissions/c61371fb-9d4a-48c6-bdeb-7b1ae3b4ac62

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
    quadraticArtinSchreierReciprocalRoot P a ha ^ 2 +
        quadraticArtinSchreierEmbedding P a ha a⁻¹ *
          quadraticArtinSchreierReciprocalRoot P a ha +
        quadraticArtinSchreierEmbedding P a ha a⁻¹ = 0 := by
  have hroot := AdjoinRoot.eval₂_root
    (quadraticArtinSchreierPolynomial P a ha)
  have hpolyEval := congrArg
    (eval₂ (AdjoinRoot.of (quadraticArtinSchreierPolynomial P a ha))
      (AdjoinRoot.root (quadraticArtinSchreierPolynomial P a ha)))
    (quadraticArtinSchreierPolynomial_eq_explicit P a ha)
  have hexplicit :
      eval₂ (AdjoinRoot.of (quadraticArtinSchreierPolynomial P a ha))
          (AdjoinRoot.root (quadraticArtinSchreierPolynomial P a ha))
          (X ^ 2 + C a⁻¹ * X + C a⁻¹) = 0 :=
    hpolyEval.symm.trans hroot
  rw [quadraticArtinSchreier_eval2_quadratic
    (AdjoinRoot.of (quadraticArtinSchreierPolynomial P a ha))
      (AdjoinRoot.root (quadraticArtinSchreierPolynomial P a ha))
      a⁻¹ a⁻¹] at hexplicit
  simpa [quadraticArtinSchreierEmbedding,
    quadraticArtinSchreierReciprocalRoot] using hexplicit
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

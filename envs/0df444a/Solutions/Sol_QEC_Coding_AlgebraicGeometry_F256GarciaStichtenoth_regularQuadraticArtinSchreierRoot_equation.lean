-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.regularQuadraticArtinSchreierRoot_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:31:22.847436+00:00
-- url     : https://prove2.me/submissions/3141bc84-934c-4165-a1df-20cd7d6e8d32

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularQuadraticStep

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    regularQuadraticArtinSchreierRoot P b hirr ^ 2 +
        regularQuadraticArtinSchreierRoot P b hirr =
      regularQuadraticArtinSchreierEmbedding P b hirr (b : K) := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  letI : CharP (RegularQuadraticArtinSchreierField P b hirr) 2 :=
    charP_of_injective_algebraMap
      (algebraMap K (RegularQuadraticArtinSchreierField P b hirr)).injective 2
  have hroot := AdjoinRoot.eval₂_root
    (regularQuadraticArtinSchreierDefiningPolynomial P b hirr)
  have hpoly : regularQuadraticArtinSchreierDefiningPolynomial P b hirr =
      X ^ 2 + X + C (b : K) := by
    rw [regularQuadraticArtinSchreierDefiningPolynomial,
      regularQuadraticArtinSchreierPolynomial_eq_explicit]
  have hpolyEval := congrArg
    (eval₂
      (AdjoinRoot.of
        (regularQuadraticArtinSchreierDefiningPolynomial P b hirr))
      (AdjoinRoot.root
        (regularQuadraticArtinSchreierDefiningPolynomial P b hirr))) hpoly
  have hexplicit :
      eval₂
          (AdjoinRoot.of
            (regularQuadraticArtinSchreierDefiningPolynomial P b hirr))
          (AdjoinRoot.root
            (regularQuadraticArtinSchreierDefiningPolynomial P b hirr))
          (X ^ 2 + X + C (b : K)) = 0 :=
    hpolyEval.symm.trans hroot
  rw [eval₂_add, eval₂_add, eval₂_X_pow, eval₂_X, eval₂_C] at hexplicit
  change AdjoinRoot.root
        (regularQuadraticArtinSchreierDefiningPolynomial P b hirr) ^ 2 +
      AdjoinRoot.root
        (regularQuadraticArtinSchreierDefiningPolynomial P b hirr) =
    AdjoinRoot.of
      (regularQuadraticArtinSchreierDefiningPolynomial P b hirr) (b : K)
  have htwo : (2 : RegularQuadraticArtinSchreierField P b hirr) = 0 :=
    CharP.cast_eq_zero (RegularQuadraticArtinSchreierField P b hirr) 2
  linear_combination hexplicit -
    AdjoinRoot.of
      (regularQuadraticArtinSchreierDefiningPolynomial P b hirr) (b : K) * htwo
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

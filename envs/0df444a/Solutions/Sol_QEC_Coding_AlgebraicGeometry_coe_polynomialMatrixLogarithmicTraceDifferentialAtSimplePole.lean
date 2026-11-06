-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.coe_polynomialMatrixLogarithmicTraceDifferentialAtSimplePole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:34:53.104035+00:00
-- url     : https://prove2.me/submissions/44064f30-7676-4054-b4f1-3cf2da087ae7

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialMatrixDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialMatrixResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_trace_map_mul_entrywiseMatrixDerivation_polynomial
attribute [local simp] QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    {n : Type*} [Fintype n] [DecidableEq n]
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (Pinv P : Matrix n n k[X]) :
    ((polynomialMatrixLogarithmicTraceDifferentialAtSimplePole p Pinv P :
      Differential.simplePoleDifferentialLattice
        (GlobalPlace.rationalAdic p)) : Differential k (RatFunc k)) =
      Matrix.trace
          ((algebraMap k[X] (RatFunc k)).mapMatrix Pinv *
            entrywiseMatrixDerivation
              (RatFuncDerivation.rationalDerivation
                (k := k) (M := RatFunc k) 1)
              ((algebraMap k[X] (RatFunc k)).mapMatrix P)) •
        functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
  unfold polynomialMatrixLogarithmicTraceDifferentialAtSimplePole
  unfold Differential.rationalAdicPolynomialDifferentialAtSimplePole
  rw [Differential.coe_rationalAdicPolynomialDifferential]
  change
    algebraMap k[X] (RatFunc k)
        (polynomialMatrixLogarithmicTrace Pinv P) •
      functionFieldDifferentialGenerator (k := k) (F := RatFunc k) = _
  unfold polynomialMatrixLogarithmicTrace
  rw [trace_map_mul_entrywiseMatrixDerivation_polynomial]
end QEC.Coding.AlgebraicGeometry

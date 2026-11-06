-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.simplePoleResidue_polynomialMatrixLogarithmicTraceDifferential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:39:34.974195+00:00
-- url     : https://prove2.me/submissions/0a267135-d7f6-4be2-99b2-b24cd9946da0

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialMatrixDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialMatrixResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_rationalAdicPolynomialDifferential


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
    Differential.simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (polynomialMatrixLogarithmicTraceDifferentialAtSimplePole p Pinv P) = 0 := by
  exact Differential.simplePoleResidue_rationalAdicPolynomialDifferential
    p (polynomialMatrixLogarithmicTrace Pinv P)
end QEC.Coding.AlgebraicGeometry

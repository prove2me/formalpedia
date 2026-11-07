-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ratFunc_prime_coordinate_quotient_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:47:06.951592+00:00
-- url     : https://prove2.me/submissions/f17327ee-ce8f-481a-ac68-146ca7f7a1a7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (K : Type*) [Field K] (p : ℕ) :
    Module.finrank (RatFunc K)
      (AdjoinRoot ((Polynomial.X : Polynomial (RatFunc K))^p - Polynomial.C RatFunc.X)) = p := by
  calc
    _ = ((Polynomial.X : Polynomial (RatFunc K))^p - Polynomial.C RatFunc.X).natDegree :=
      finrank_quotient_span_eq_natDegree
    _ = p := Polynomial.natDegree_X_pow_sub_C
end QEC.Coding.AlgebraicGeometry

-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ratFunc_kronecker_quotient_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:25:34.758477+00:00
-- url     : https://prove2.me/submissions/8bb18bd9-7900-4a54-8c08-208854771717

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
    (K : Type*) [Field K] (p : ℕ) (hp : p.Prime) :
    Module.finrank (RatFunc K)
      (AdjoinRoot (((Polynomial.X : Polynomial (RatFunc K)) -
        Polynomial.C ((RatFunc.X : RatFunc K)^p)) *
        ((Polynomial.X : Polynomial (RatFunc K))^p - Polynomial.C RatFunc.X))) = p+1 := by
  calc
    _ = (((Polynomial.X : Polynomial (RatFunc K)) -
        Polynomial.C ((RatFunc.X : RatFunc K)^p)) *
        ((Polynomial.X : Polynomial (RatFunc K))^p - Polynomial.C RatFunc.X)).natDegree :=
      finrank_quotient_span_eq_natDegree
    _ = p+1 := by
      rw [Polynomial.natDegree_mul
      (Polynomial.X_sub_C_ne_zero ((RatFunc.X : RatFunc K)^p))
      (Polynomial.X_pow_sub_C_ne_zero hp.pos RatFunc.X),
    Polynomial.natDegree_X_sub_C,Polynomial.natDegree_X_pow_sub_C,Nat.add_comm]
end QEC.Coding.AlgebraicGeometry

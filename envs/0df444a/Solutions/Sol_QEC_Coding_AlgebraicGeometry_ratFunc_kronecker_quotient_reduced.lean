-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ratFunc_kronecker_quotient_reduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:22:41.007571+00:00
-- url     : https://prove2.me/submissions/9a768ce2-4b46-448e-af20-f51be1be9b9b

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
    IsReduced (AdjoinRoot (((Polynomial.X : Polynomial (RatFunc K)) -
      Polynomial.C ((RatFunc.X : RatFunc K)^p)) *
      ((Polynomial.X : Polynomial (RatFunc K))^p - Polynomial.C RatFunc.X))) := by
  apply (Ideal.isRadical_iff_quotient_reduced _).mp
  exact isRadical_iff_span_singleton.mp
    (ratFunc_kronecker_product_squarefree K p hp).isRadical
end QEC.Coding.AlgebraicGeometry

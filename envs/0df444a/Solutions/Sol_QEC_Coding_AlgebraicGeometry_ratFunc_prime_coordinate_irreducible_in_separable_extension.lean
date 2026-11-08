-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ratFunc_prime_coordinate_irreducible_in_separable_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:23:18.885081+00:00
-- url     : https://prove2.me/submissions/0a878d71-9725-443f-8054-8268b4cb03f0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ratFunc_coordinate_not_prime_power_in_separable_extension

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (K E : Type*) [Field K] [Field E] [Algebra (RatFunc K) E]
    [Algebra.IsSeparable (RatFunc K) E]
    (p : ℕ) [ExpChar (RatFunc K) p] (hp : p.Prime) :
    Irreducible ((Polynomial.X : Polynomial E)^p -
      Polynomial.C (algebraMap (RatFunc K) E RatFunc.X)) :=
  _root_.X_pow_sub_C_irreducible_of_prime hp
    (ratFunc_coordinate_not_prime_power_in_separable_extension K E p hp)
end QEC.Coding.AlgebraicGeometry

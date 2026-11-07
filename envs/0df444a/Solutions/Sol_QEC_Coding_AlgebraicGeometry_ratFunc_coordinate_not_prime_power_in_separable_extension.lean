-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ratFunc_coordinate_not_prime_power_in_separable_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:49:26.8544+00:00
-- url     : https://prove2.me/submissions/8dcc2a09-3b9c-4718-954b-ac9e8f34c087

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_separable_extension_not_prime_power

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (K E : Type*) [Field K] [Field E] [Algebra (RatFunc K) E]
    [Algebra.IsSeparable (RatFunc K) E]
    (p : ℕ) [ExpChar (RatFunc K) p] (hp : p.Prime) (u : E) :
    u^p ≠ algebraMap (RatFunc K) E RatFunc.X :=
  separable_extension_not_prime_power (RatFunc K) E p RatFunc.X
    (ratFunc_coordinate_not_prime_power K p hp) u
end QEC.Coding.AlgebraicGeometry

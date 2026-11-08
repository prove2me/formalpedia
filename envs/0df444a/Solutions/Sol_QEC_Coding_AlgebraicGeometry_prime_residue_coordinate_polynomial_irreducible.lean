-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.prime_residue_coordinate_polynomial_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:22:18.460199+00:00
-- url     : https://prove2.me/submissions/5d8bad6d-3f34-451c-90dc-7efa1303f58b

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
    (p : ℕ) [Fact p.Prime] :
    Irreducible ((Polynomial.X : Polynomial (RatFunc (ZMod p)))^p -
      Polynomial.C RatFunc.X) :=
  ratFunc_prime_coordinate_polynomial_irreducible (ZMod p) p Fact.out
end QEC.Coding.AlgebraicGeometry

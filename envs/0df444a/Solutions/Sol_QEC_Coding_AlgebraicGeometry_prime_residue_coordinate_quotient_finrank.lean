-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.prime_residue_coordinate_quotient_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:22:28.109255+00:00
-- url     : https://prove2.me/submissions/d0a2b1fe-06f0-4003-a2a8-83cc9c79642d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ratFunc_prime_coordinate_quotient_finrank

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] :
    Module.finrank (RatFunc (ZMod p))
      (AdjoinRoot ((Polynomial.X : Polynomial (RatFunc (ZMod p)))^p -
        Polynomial.C RatFunc.X)) = p :=
  ratFunc_prime_coordinate_quotient_finrank (ZMod p) p
end QEC.Coding.AlgebraicGeometry

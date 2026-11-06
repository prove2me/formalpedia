-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.PrimeFrobenius.primeAlgebraFrobenius_comp_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:54:59.56584+00:00
-- url     : https://prove2.me/submissions/fa24205f-259c-4320-abb1-7c2217b51dde

import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeAlgebraFrobenius
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_PrimeFrobenius_primeAlgebraFrobenius_constant

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.PrimeFrobenius
noncomputable section
variable (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [Algebra (ZMod p) R]
namespace QEC.Coding.AlgebraicGeometry.PrimeFrobenius
theorem _root_.solution :
    (primeAlgebraFrobenius p R).comp (algebraMap (ZMod p) R) = algebraMap (ZMod p) R := by
  ext a
  exact primeAlgebraFrobenius_constant p R a
end QEC.Coding.AlgebraicGeometry.PrimeFrobenius

-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.PrimeFrobenius.primeAlgebraFrobenius_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:56:23.066281+00:00
-- url     : https://prove2.me/submissions/5db92d56-f601-4d2c-b614-9731c8d4067b

import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeAlgebraFrobenius

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.PrimeFrobenius
noncomputable section
variable (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [Algebra (ZMod p) R]
namespace QEC.Coding.AlgebraicGeometry.PrimeFrobenius
theorem _root_.solution (a : ZMod p) :
    primeAlgebraFrobenius p R (algebraMap (ZMod p) R a) = algebraMap (ZMod p) R a := by
  change (algebraMap (ZMod p) R a)^p = algebraMap (ZMod p) R a
  rw [← map_pow, ZMod.pow_card]
end QEC.Coding.AlgebraicGeometry.PrimeFrobenius

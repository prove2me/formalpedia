-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.PrimeFrobenius.primeAlgebraFrobenius_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:55:00.414001+00:00
-- url     : https://prove2.me/submissions/d1a152d5-5502-4a61-a893-93a0e59d3d46

import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeAlgebraFrobenius

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.PrimeFrobenius
noncomputable section
variable (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [Algebra (ZMod p) R]
namespace QEC.Coding.AlgebraicGeometry.PrimeFrobenius
theorem _root_.solution : (primeAlgebraFrobenius p R).IsIntegral := by
  intro x
  refine ⟨Polynomial.X^p - Polynomial.C x,
    Polynomial.monic_X_pow_sub_C x (Fact.out : p.Prime).ne_zero, ?_⟩
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
  change x^p - x^p = 0
  exact sub_self _
end QEC.Coding.AlgebraicGeometry.PrimeFrobenius

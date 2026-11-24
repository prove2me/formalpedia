-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_exists_int_relation_bf34191512a6
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T05:52:05.996637+00:00
-- url     : https://prove2.me/submissions/25315036-4c42-4754-8afb-2071f2d45b3d

import Mathlib


theorem solution (r : AlgebraicClosure ℚ) :
    ∃ g : Polynomial ℤ, g ≠ 0 ∧ Polynomial.aeval r g = 0 := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert! AlgebraicClosure.isAlgebraic ℚ using 1 <;> apply Subsingleton.elim
  exact (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr (Algebra.IsAlgebraic.isAlgebraic r)

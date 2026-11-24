-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_algebraMap_mvPolynomial_int_complex_a208a4dfdd5b
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T01:30:14.435186+00:00
-- url     : https://prove2.me/submissions/c340d293-1efc-4aa5-b007-d348e4648251

import Mathlib
attribute [local instance] MvPolynomial.algebraMvPolynomial


theorem solution (σ : Type) :
    algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℂ) = MvPolynomial.map (Int.castRingHom ℂ) := by
  rfl

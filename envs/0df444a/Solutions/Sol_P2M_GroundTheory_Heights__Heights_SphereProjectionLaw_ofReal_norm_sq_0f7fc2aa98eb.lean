-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_ofReal_norm_sq_0f7fc2aa98eb
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T05:44:33.086901+00:00
-- url     : https://prove2.me/submissions/c166df19-812b-4773-8598-6a241a34a8ae

import Mathlib


theorem solution (x : ℂ) : ((‖x‖ ^ 2 : ℝ) : ℂ) = x * star x := by
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self, starRingEnd_apply, mul_comm]

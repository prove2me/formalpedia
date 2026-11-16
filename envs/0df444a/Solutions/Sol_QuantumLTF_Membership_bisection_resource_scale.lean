-- Prove2me | solution 1 for QuantumLTF.Membership.bisection_resource_scale
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T20:14:38.02728+00:00
-- url     : https://prove2.me/submissions/4fa2323c-3386-4e1e-941d-4baca910660b

import Mathlib

theorem solution {A L U q : ℝ}
    (hA : 0 ≤ A) (hL : 1 ≤ L) (hU : 0 ≤ U) (hq0 : 0 ≤ q)
    (hq : q ≤ U * L) :
    (A + q) ^ 2 * (q + 1) ≤ (U + 1) ^ 3 * (A + L) ^ 2 * L := by
  have hK : 0 ≤ U + 1 := by linarith
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  have hAL : 0 ≤ A + L := by linarith
  have hAq : 0 ≤ A + q := by linarith
  have hbase : A + q ≤ (U + 1) * (A + L) := by
    nlinarith [mul_nonneg hU hA, mul_nonneg hU hL0]
  have hround : q + 1 ≤ (U + 1) * L := by
    nlinarith
  have hsq : (A + q) ^ 2 ≤ ((U + 1) * (A + L)) ^ 2 :=
    (sq_le_sq₀ hAq (mul_nonneg hK hAL)).2 hbase
  calc
    (A + q) ^ 2 * (q + 1)
        ≤ ((U + 1) * (A + L)) ^ 2 * ((U + 1) * L) :=
          mul_le_mul hsq hround (by positivity) (by positivity)
    _ = (U + 1) ^ 3 * (A + L) ^ 2 * L := by ring

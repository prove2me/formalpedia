-- Prove2me | solution 1 for WardropTraffic.Signal.dTdy_corner_neg
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T02:17:56.472191+00:00
-- url     : https://prove2.me/submissions/59eb38b5-17a9-4ab2-bf82-e0037e29c7e5

import Mathlib
import Definitions.Def_WardropTraffic_Signal_Setting

theorem solution (lam mu xi eta : ℝ) (hmu : 0 < mu) (hlm : mu ≤ lam)
    (heta0 : 0 < eta) (heta1 : eta < 1) (hsum : 1 < xi + eta) :
    mu * eta ^ 2 - lam * xi ^ 2 - 2 * mu * eta * (1 - xi) =
        mu * (eta ^ 2 - 2 * eta + 2 * xi * eta) - lam * xi ^ 2 ∧
      mu * (eta ^ 2 - 2 * eta + 2 * xi * eta) - lam * xi ^ 2 =
        -mu * (2 * eta * (1 - eta) + (xi - eta) ^ 2) - (lam - mu) * xi ^ 2 ∧
      (mu * eta ^ 2 - lam * xi ^ 2 - 2 * mu * eta * (1 - xi)) / (xi + eta - 1) ^ 2 < 0 := by
  refine ⟨by ring, by ring, ?_⟩
  apply div_neg_of_neg_of_pos
  · have hpos : 0 < mu * (2 * eta * (1 - eta)) := by positivity
    have hnon : 0 ≤ (lam - mu) * xi ^ 2 := by positivity
    have hsq : 0 ≤ mu * (xi - eta) ^ 2 := by positivity
    nlinarith
  · exact sq_pos_of_pos (by linarith)

#print axioms solution

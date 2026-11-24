-- Prove2me | solution 1 for SensitivityGraphPopulation.minimumEdges_succ
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:20:31.411153+00:00
-- url     : https://prove2.me/submissions/12eb5027-ac6a-495f-9563-1f12175d0448

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_IntegralGraphPopulation
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SensitivityGraphPopulation
end SensitivityGraphPopulation


/-! Discrete convexity of the exact minimum-edge function. -/
open SensitivityGraphPopulation
open scoped Classical
set_option autoImplicit false

theorem solution (n alpha : ℕ) (hpos : 0 < alpha) :
    minimumEdges (n + 1) alpha = minimumEdges n alpha + n / alpha := by
  have hn := Nat.mod_add_div n alpha
  have hn1 := Nat.mod_add_div (n + 1) alpha
  by_cases hdvd : alpha ∣ n + 1
  · have hdiv := Nat.succ_div_of_dvd hdvd
    have hmod := Nat.mod_eq_zero_of_dvd hdvd
    rw [hdiv, hmod] at hn1
    have hrem : n % alpha + 1 = alpha := by nlinarith only [hn, hn1]
    unfold minimumEdges
    rw [hdiv, hmod, Nat.choose_succ_succ' _ 1, Nat.choose_one_right]
    simp only [Nat.reduceAdd, Nat.zero_mul]
    have hmul := congrArg (fun r => r * (n / alpha)) hrem
    nlinarith only [hmul]
  · have hdiv := Nat.succ_div_of_not_dvd hdvd
    rw [hdiv] at hn1
    have hrem : (n + 1) % alpha = n % alpha + 1 := by omega
    unfold minimumEdges
    rw [hdiv, hrem]
    ring

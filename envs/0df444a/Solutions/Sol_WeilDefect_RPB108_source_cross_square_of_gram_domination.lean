-- Prove2me | solution 1 for WeilDefect.RPB108.source_cross_square_of_gram_domination
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T03:58:57.481435+00:00
-- url     : https://prove2.me/submissions/e6cbce6f-e03f-4d52-87d8-1eec687e27cf

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem solution (q : ℂ) (c rho G V : ℝ)
    (hc : 0 ≤ c) (hG : G ≤ rho*V) (hq : ‖q‖^2 ≤ c*G) :
    ‖q‖^2 ≤ (c*rho)*V := by
  calc
    ‖q‖^2 ≤ c*G := hq
    _ ≤ c*(rho*V) := mul_le_mul_of_nonneg_left hG hc
    _ = (c*rho)*V := by ring

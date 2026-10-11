-- Prove2me | solution 1 for WeilDefect.RPB108.paid_actual_energy_lower
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:00:04.637595+00:00
-- url     : https://prove2.me/submissions/da485f74-f2fc-4858-8b39-02c9060db3e8

import Theorems.Thm_WeilDefect_RPB108_paid_young_lower
import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem solution (A M theta x V v : ℝ) (p q : ℂ)
    (ht0 : 0 ≤ theta) (ht1 : theta < 1) (hx : 0 ≤ x)
    (hV : 0 ≤ V) (hv : v ≤ V) (hpq : ‖p-q‖ ≤ M*Real.sqrt V) :
    (A-M^2/(1-theta))*x^2+theta*v ≤ A*x^2-2*x*‖p-q‖+V := by
  have hy := paid_young_lower A M theta x (Real.sqrt V) ht1
  rw [abs_of_nonneg (mul_nonneg hx (Real.sqrt_nonneg _)), Real.sq_sqrt hV] at hy
  have hcross := mul_le_mul_of_nonneg_left hpq (show 0 ≤ 2*x by positivity)
  have hlower := mul_le_mul_of_nonneg_left hv ht0
  nlinarith only [hy, hcross, hlower]

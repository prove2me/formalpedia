-- Prove2me | solution 1 for WeilDefect.RPB108.native_row_square_of_energy_floor
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:31:12.843541+00:00
-- url     : https://prove2.me/submissions/bc15d0f4-7d4c-46ec-896f-24f1af6676f1

import Theorems.Thm_WeilDefect_RPB108_complex_row_square_le
import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem solution {ι : Type*} [Fintype ι]
    (a z : ι → ℂ) (b : ι → ℝ) (g d V : ℝ)
    (hb : ∀ i, ‖a i‖ ≤ b i) (hd : 0 ≤ d)
    (hbudget : (∑ i, (b i)^2) ≤ d*g)
    (hfloor : g*(∑ i, ‖z i‖^2) ≤ V) :
    ‖∑ i, a i*z i‖^2 ≤ d*V := by
  calc
    ‖∑ i, a i*z i‖^2 ≤ (∑ i, (b i)^2)*(∑ i, ‖z i‖^2) :=
      complex_row_square_le a z b hb
    _ ≤ (d*g)*(∑ i, ‖z i‖^2) :=
      mul_le_mul_of_nonneg_right hbudget (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = d*(g*(∑ i, ‖z i‖^2)) := by ring
    _ ≤ d*V := mul_le_mul_of_nonneg_left hfloor hd

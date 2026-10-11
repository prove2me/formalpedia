-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Even.retained_energy_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T03:21:02.62619+00:00
-- url     : https://prove2.me/submissions/ace56ab1-07fa-439e-bdaa-e961ed80fd7a

import Theorems.Thm_WeilDefect_RPB108_DNE27Even_retainedLower_pos
import Definitions.Def_RPB108_DNE27MixedEnergy_Even
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Even
theorem solution (z : Fin 4 → ℂ) : 0 ≤ retainedEnergy z := by
  unfold retainedEnergy
  exact mul_nonneg retainedLower_pos.le (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

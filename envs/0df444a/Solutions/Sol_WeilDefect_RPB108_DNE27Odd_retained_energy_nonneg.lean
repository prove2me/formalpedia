-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Odd.retained_energy_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T03:20:10.627364+00:00
-- url     : https://prove2.me/submissions/afcc60b3-1ed1-4f2c-a239-ff8c10511072

import Theorems.Thm_WeilDefect_RPB108_DNE27Odd_retainedLower_pos
import Definitions.Def_RPB108_DNE27MixedEnergy_Odd
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Odd
theorem solution (z : Fin 4 → ℂ) : 0 ≤ retainedEnergy z := by
  unfold retainedEnergy
  exact mul_nonneg retainedLower_pos.le (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

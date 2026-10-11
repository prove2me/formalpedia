-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Odd.native_pairing_normalization
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:27:48.296567+00:00
-- url     : https://prove2.me/submissions/fc173156-21e0-4774-8de3-18284bbcb340

import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Odd
import Definitions.Def_RPB108_DNE27NativePairing_Odd
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Odd

theorem solution (a : Fin 3 → ℝ) (z : Fin 4 → ℂ) :
    nativePairing a z = ∑ i : Fin 3, (a i : ℂ)*((gramScales i : ℂ)*z i.succ) := by
  unfold nativePairing
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

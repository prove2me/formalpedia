-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Even.native_pairing_normalization
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:27:25.920615+00:00
-- url     : https://prove2.me/submissions/87d17d2a-ef25-408e-82fd-f51c19bd716d

import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Even
import Definitions.Def_RPB108_DNE27NativePairing_Even
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Even

theorem solution (a : Fin 3 → ℝ) (z : Fin 4 → ℂ) :
    nativePairing a z = ∑ i : Fin 3, (a i : ℂ)*((gramScales i : ℂ)*z i.succ) := by
  unfold nativePairing
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

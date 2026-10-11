-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Even.mixed_diagonal_lower
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T03:23:48.471785+00:00
-- url     : https://prove2.me/submissions/bf3e3799-4e70-4a35-97dc-e81d9c30c11d

import Theorems.Thm_WeilDefect_RPB108_DNE27Even_threeLower_identity
import Theorems.Thm_WeilDefect_RPB108_DNE27Even_paid_mixed_lower
import Theorems.Thm_WeilDefect_RPB108_DNE27Even_retained_energy_nonneg
import Definitions.Def_RPB108_DNE27MixedEnergy_Even
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Even
theorem solution (z : Fin 4 → ℂ) :
    (∑ i, lower i*‖z i‖^2) ≤
      nativeLow*‖z 0‖^2-2*mixedUpper*(‖z 0‖*Real.sqrt (retainedEnergy z)) +
        retainedEnergy z := by
  have hp := paid_mixed_lower ‖z 0‖ (Real.sqrt (retainedEnergy z))
  rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)),
    Real.sq_sqrt (retained_energy_nonneg z)] at hp
  have hs : (∑ i, lower i*‖z i‖^2) = lowLower*‖z 0‖^2+theta*retainedEnergy z := by
    simp [lower, retainedEnergy, Fin.sum_univ_succ, threeLower_identity]
    ring
  exact hs.trans_le hp

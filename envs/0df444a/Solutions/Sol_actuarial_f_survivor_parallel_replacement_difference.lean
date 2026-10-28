-- Prove2me | solution 1 for actuarial_f_survivor_parallel_replacement_difference
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:01:41.776695+00:00
-- url     : https://prove2.me/submissions/2fa63076-b97f-4f08-82c9-999c6d9502d7

import Mathlib
import Definitions.Def_actuarial_f_gmpProtectedSurvivorParallel
import Definitions.Def_actuarial_f_gmpProtectedSurvivorReplacement
import Definitions.Def_actuarial_f_gmpProtectedSurvivorDisplaceable
open ActuarialUnderpinsF

theorem solution
    (replace : Prop) (scheme statutory : ℝ) :
    gmpProtectedSurvivorParallel scheme statutory =
      gmpProtectedSurvivorReplacement replace scheme statutory +
      gmpProtectedSurvivorDisplaceable replace scheme statutory := by
  unfold gmpProtectedSurvivorParallel gmpProtectedSurvivorReplacement gmpProtectedSurvivorDisplaceable
  split_ifs
  · rcases le_total scheme statutory with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · unfold gmpProtectedSurvivorParallel; ring

-- Prove2me | solution 1 for actuarial_f_survivor_protection_when_guarantee_due
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:54:56.171987+00:00
-- url     : https://prove2.me/submissions/6d0563a1-59eb-4c5f-ba5c-a2873ea442e8

import Mathlib
import Definitions.Def_actuarial_f_gmpProtectedSurvivorReplacement
open ActuarialUnderpinsF

theorem solution
    (scheme statutory : ℝ) :
    gmpProtectedSurvivorReplacement True scheme statutory = statutory := by
  simp [gmpProtectedSurvivorReplacement]

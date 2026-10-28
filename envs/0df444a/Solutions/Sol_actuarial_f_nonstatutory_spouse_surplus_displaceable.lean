-- Prove2me | solution 1 for actuarial_f_nonstatutory_spouse_surplus_displaceable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:56:23.325304+00:00
-- url     : https://prove2.me/submissions/8c31a65b-2310-44d0-93bb-74530f6387e6

import Mathlib
import Definitions.Def_actuarial_f_gmpProtectedSurvivorDisplaceable
open ActuarialUnderpinsF

theorem solution
    (scheme statutory : ℝ) :
    gmpProtectedSurvivorDisplaceable True scheme statutory =
      max 0 (scheme - statutory) := by
  simp [gmpProtectedSurvivorDisplaceable]

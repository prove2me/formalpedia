-- Prove2me | solution 1 for actuarial_f_survivor_parallel_respects_floor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:53:33.036483+00:00
-- url     : https://prove2.me/submissions/26426979-060a-4c51-a1a5-697d48322637

import Mathlib
import Definitions.Def_actuarial_f_gmpProtectedSurvivorParallel
open ActuarialUnderpinsF

theorem solution
    (scheme statutory : ℝ) :
    statutory ≤ gmpProtectedSurvivorParallel scheme statutory := by
  exact le_max_right _ _

-- Prove2me | solution 1 for actuarial_e_spouse_deferred_after_settlement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:31:21.701219+00:00
-- url     : https://prove2.me/submissions/276f3b12-cde8-42f0-9244-519b6ebcf518

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_spouseDue

open ActuarialDeathE



theorem solution (i j : ℕ) : spouseDue i j (i + 1) = 0 := by
  unfold spouseDue
  rw [if_neg (by omega)]


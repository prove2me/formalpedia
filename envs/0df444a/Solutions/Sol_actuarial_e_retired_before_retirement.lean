-- Prove2me | solution 1 for actuarial_e_retired_before_retirement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:17:40.195984+00:00
-- url     : https://prove2.me/submissions/b2423add-1982-4c0f-8c98-d0ed52cc0b73

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_retired

open ActuarialDeathE

theorem solution (h r i : ℕ) (hi : i < r) : retired h r i = 0 := by
  unfold retired
  rw [if_neg (by omega)]

-- Prove2me | solution 1 for actuarial_e_scheduled_annual_unit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:18:26.63233+00:00
-- url     : https://prove2.me/submissions/205ec68a-26b9-402a-87f0-2ef2870146db

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_scheduled

open ActuarialDeathE

theorem solution (t : ℕ) : scheduled 1 t = 1 := by
  unfold scheduled
  rw [if_pos ⟨Nat.one_pos, Nat.mod_one t⟩]

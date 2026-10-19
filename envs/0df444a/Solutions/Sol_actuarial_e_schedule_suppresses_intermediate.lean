-- Prove2me | solution 1 for actuarial_e_schedule_suppresses_intermediate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:18:19.119049+00:00
-- url     : https://prove2.me/submissions/0068f7dc-271c-45f9-83b1-363efa1d468c

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

theorem solution (m t : ℕ) (ht : t % m ≠ 0) : scheduled m t = 0 := by
  unfold scheduled
  rw [if_neg (fun h => ht h.2)]

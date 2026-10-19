-- Prove2me | solution 1 for actuarial_e_retired_from_retirement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:17:55.819716+00:00
-- url     : https://prove2.me/submissions/75e1d789-9e8e-4ac7-a933-c366772050dc

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

theorem solution (h r i : ℕ) (hi : i < h) (hr : r ≤ i) : retired h r i = 1 := by
  unfold retired
  rw [if_pos ⟨hi, hr⟩]

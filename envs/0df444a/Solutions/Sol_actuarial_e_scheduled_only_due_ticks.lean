-- Prove2me | solution 1 for actuarial_e_scheduled_only_due_ticks
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:18:34.240521+00:00
-- url     : https://prove2.me/submissions/d1ee1bd7-d871-40f7-a058-5ef65da04624

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

theorem solution (m t : ℕ) (hm : 0 < m) (ht : t % m = 0) : scheduled m t = 1 := by
  unfold scheduled
  rw [if_pos ⟨hm, ht⟩]

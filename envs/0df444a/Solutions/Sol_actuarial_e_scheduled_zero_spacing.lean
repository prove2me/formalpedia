-- Prove2me | solution 1 for actuarial_e_scheduled_zero_spacing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:18:41.862561+00:00
-- url     : https://prove2.me/submissions/7c3ed4db-806d-43c1-bc70-ba75e8090654

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

theorem solution (t : ℕ) : scheduled 0 t = 0 := by
  unfold scheduled
  rw [if_neg (fun h => (lt_irrefl 0) h.1)]

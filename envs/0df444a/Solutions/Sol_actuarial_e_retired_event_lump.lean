-- Prove2me | solution 1 for actuarial_e_retired_event_lump
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:17:47.837776+00:00
-- url     : https://prove2.me/submissions/bf65d94d-7d2e-47af-8af7-674b818a54f6

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_regimeLump

open ActuarialDeathE

theorem solution (h e r i : ℕ) (service defer retire : ℕ → ℝ) (he : e ≤ r) (hi : i < h) (hr : r ≤ i) : regimeLump h e r i service defer retire = retire (i + 1) := by
  unfold regimeLump active deferred retired
  rw [if_neg (by omega), if_neg (by omega), if_pos ⟨hi, hr⟩]
  ring

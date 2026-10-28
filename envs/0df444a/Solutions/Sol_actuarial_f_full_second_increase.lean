-- Prove2me | solution 1 for actuarial_f_full_second_increase
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:41:24.85815+00:00
-- url     : https://prove2.me/submissions/ec26536d-e83c-4c68-9daa-29605b8c6f42

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiRate
import Definitions.Def_actuarial_f_monthlyScheduledRate

open ActuarialUnderpinsF

theorem solution
    (r first : ℕ) (floor cap : ℝ) (inflation : ℕ → ℝ)
    (hr : r < first) :
    monthlyScheduledRate r first floor cap inflation (first + 12) =
      lpiRate floor cap (inflation 1) := by
  unfold monthlyScheduledRate
  rw [if_neg (by omega), if_pos (by omega), show (first + 12 - first) / 12 = 1 by omega]

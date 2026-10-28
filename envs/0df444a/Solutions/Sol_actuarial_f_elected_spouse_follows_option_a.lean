-- Prove2me | solution 1 for actuarial_f_elected_spouse_follows_option_a
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:59:34.354287+00:00
-- url     : https://prove2.me/submissions/2bd4fdb2-9745-428b-ae11-7fe7125d2841

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_linkedSpouseBasis

open ActuarialUnderpinsF



theorem solution
    (a b : ℕ → ℝ) (sa sb : ℕ → ℕ → ℝ)
    (z i : ℕ) (hab : b z < a z) :
    linkedSpouseBasis a b sa sb z i = sa z i := by
  simp [linkedSpouseBasis, not_le.mpr hab]

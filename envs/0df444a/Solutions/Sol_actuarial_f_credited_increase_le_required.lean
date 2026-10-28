-- Prove2me | solution 1 for actuarial_f_credited_increase_le_required
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:01:14.215463+00:00
-- url     : https://prove2.me/submissions/fbf0d650-ef6d-46f2-8517-062eb810492e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_pensionIncreaseOutstanding

open ActuarialUnderpinsF



theorem solution
    (required credited : ℝ) (h : 0 ≤ credited)
    (hr : 0 ≤ required) :
    pensionIncreaseOutstanding required credited ≤ required := by
  exact max_le hr (by linarith)

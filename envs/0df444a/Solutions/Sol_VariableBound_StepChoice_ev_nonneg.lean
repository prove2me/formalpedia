-- Prove2me | solution 1 for VariableBound.StepChoice.ev_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:24:37.645909+00:00
-- url     : https://prove2.me/submissions/a77a3db3-0ac1-4b1b-862a-fe174b8d581e

import Definitions.Def_VariableBound_StepChoice
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution (q : ℕ) : 0 ≤ ParityChecks.ev q := by
  unfold ParityChecks.ev
  split <;> norm_num

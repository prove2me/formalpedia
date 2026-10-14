-- Prove2me | solution 1 for actuarial_c_zero_term_zero_loss
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:36.428236+00:00
-- url     : https://prove2.me/submissions/fc131dd0-2c80-4c97-b59d-0968ec40396f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_premiumPath
import Definitions.Def_actuarial_c_lossPath
import Definitions.Def_actuarial_c_expectedLoss

open ActuarialAssurances

theorem solution (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) : expectedLoss h 0 v 0 b p=0 := by
  simp [expectedLoss, lossPath, premiumPath, alive, termPath, death]

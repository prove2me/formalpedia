-- Prove2me | solution 1 for actuarial_c_endow_now
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:34.310069+00:00
-- url     : https://prove2.me/submissions/d47c1cc4-7a08-4833-aad7-a90ddf1183d1

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_total
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_purePath
import Definitions.Def_actuarial_c_endowPath
import Definitions.Def_actuarial_c_endow

open ActuarialAssurances

theorem solution (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) : endow h 0 v b p=total h p := by
  simp [endow, endowPath, purePath, alive, termPath, death, total]

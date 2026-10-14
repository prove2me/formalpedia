-- Prove2me | solution 1 for actuarial_c_delay_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:34.213329+00:00
-- url     : https://prove2.me/submissions/c9954f17-15d5-44c1-8fd0-4bffa6dde5a3

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv
import Definitions.Def_actuarial_c_delayPath
import Definitions.Def_actuarial_c_delayEPV

open ActuarialAssurances

theorem solution (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) : delayEPV h 0 v b p=epv h v b p := by
  simp [delayEPV, delayPath, death, epv, path]

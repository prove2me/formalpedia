-- Prove2me | solution 1 for actuarial_c_zero_assured
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:36.21265+00:00
-- url     : https://prove2.me/submissions/6bda79df-a4f1-4012-8655-5350ea04260f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv

open ActuarialAssurances

theorem solution (h : ℕ) (v : ℝ) (p : ℕ → ℝ) : epv h v (fun _ => 0) p=0 := by
  simp [epv, path, death]

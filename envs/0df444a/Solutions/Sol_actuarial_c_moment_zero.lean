-- Prove2me | solution 1 for actuarial_c_moment_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:35.612745+00:00
-- url     : https://prove2.me/submissions/74b94926-ed92-4f09-ab4a-ddb081f08791

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_second

open ActuarialAssurances

theorem solution (h : ℕ) (v : ℝ) (p : ℕ → ℝ) : second h v (fun _ => 0) p=0 := by
  simp [second, path, death]

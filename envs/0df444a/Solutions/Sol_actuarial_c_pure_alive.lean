-- Prove2me | solution 1 for actuarial_c_pure_alive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:50:52.334398+00:00
-- url     : https://prove2.me/submissions/a84bdc1f-a395-4086-a16f-a2472b201280

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_purePath

open ActuarialAssurances

theorem solution (n k : ℕ) (v : ℝ) (hk : n ≤ k) : purePath n k v=v^n := by
  simp only [purePath, alive]
  grind

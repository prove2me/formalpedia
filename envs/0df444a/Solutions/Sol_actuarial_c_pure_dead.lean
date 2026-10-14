-- Prove2me | solution 1 for actuarial_c_pure_dead
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:50:53.666284+00:00
-- url     : https://prove2.me/submissions/5716113e-56bb-4c6a-a983-1e1c8e2e76a8

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_purePath

open ActuarialAssurances

theorem solution (n k : ℕ) (v : ℝ) (hk : k < n) : purePath n k v=0 := by
  simp only [purePath, alive]
  grind

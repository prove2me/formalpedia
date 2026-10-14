-- Prove2me | solution 1 for actuarial_d_alive_until
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:36.278165+00:00
-- url     : https://prove2.me/submissions/77cea7fe-61d4-4f19-8673-60459dd399ee

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_dead

open ActuarialJointD

theorem solution (i : ℕ) : alive i i = 1 := by
  simp [dead, alive]

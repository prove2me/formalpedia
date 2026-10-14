-- Prove2me | solution 1 for actuarial_d_alive_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:36.844781+00:00
-- url     : https://prove2.me/submissions/10b8da69-18e5-4f16-8c3c-a699fe6409ac

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_dead

open ActuarialJointD

theorem solution (i : ℕ) : alive i 0 = 1 := by
  simp [dead, alive]

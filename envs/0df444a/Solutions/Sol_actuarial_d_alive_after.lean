-- Prove2me | solution 1 for actuarial_d_alive_after
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:36.799987+00:00
-- url     : https://prove2.me/submissions/205393b6-353a-4194-94d9-e1714c3b8e75

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_dead

open ActuarialJointD

theorem solution (i : ℕ) : alive i (i+1) = 0 := by
  simp [dead, alive]

-- Prove2me | solution 1 for actuarial_d_dead_after
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:37.358738+00:00
-- url     : https://prove2.me/submissions/59d62f4a-6a8d-4b38-a974-6371c1494850

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_dead

open ActuarialJointD

theorem solution (i : ℕ) : dead i (i+1) = 1 := by
  simp [dead, alive]

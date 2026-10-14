-- Prove2me | solution 1 for actuarial_d_defer_zero_term
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:37.950707+00:00
-- url     : https://prove2.me/submissions/27bcaf66-1302-44dc-8343-bb9b1603cccd

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_deferLast

open ActuarialJointD

theorem solution (h a n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : deferLast h a 0 p d b = 0 := by
  simp [deferLast, deferValue, annRange, expect, last, onlyY, dead, alive, onlyX, both]

-- Prove2me | solution 1 for actuarial_d_pure_last_zero_discount
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:39.10741+00:00
-- url     : https://prove2.me/submissions/cc8f2f44-25e0-487c-8b14-ee592722246a

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_pureLast
import Definitions.Def_actuarial_d_plast

open ActuarialJointD

theorem solution (h t : ℕ) (p : ℕ → ℕ → ℝ) : pureLast h t p (fun _ => 0) = 0 := by
  simp [plast, expect, last, onlyY, dead, alive, onlyX, both, pureLast]

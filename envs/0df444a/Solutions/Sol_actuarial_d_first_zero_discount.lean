-- Prove2me | solution 1 for actuarial_d_first_zero_discount
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:38.02268+00:00
-- url     : https://prove2.me/submissions/e33cb134-951a-4647-88c0-86a541e05c9c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_assureFirst
import Definitions.Def_actuarial_d_firstPath
import Definitions.Def_actuarial_d_expect

open ActuarialJointD

theorem solution (h : ℕ) (p : ℕ → ℕ → ℝ) : assureFirst h p (fun _ => 0) = 0 := by
  simp [expect, firstPath, assureFirst]

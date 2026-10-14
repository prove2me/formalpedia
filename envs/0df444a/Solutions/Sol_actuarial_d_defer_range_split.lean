-- Prove2me | solution 1 for actuarial_d_defer_range_split
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T13:09:12.49891+00:00
-- url     : https://prove2.me/submissions/ebcece43-c9fc-4585-8ca7-af0502fe7761

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_annRange

open ActuarialJointD

theorem solution (a n m : ℕ) (d b s : ℕ → ℝ) : annRange a (n+m) d b s = annRange a n d b s + annRange (a+n) m d b s := by
  simp only [annRange]
  rw [Finset.sum_range_add]
  simp [Nat.add_assoc]


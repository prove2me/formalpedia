-- Prove2me | solution 1 for actuarial_c_decrease_last
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:54:03.979081+00:00
-- url     : https://prove2.me/submissions/ff97f8ee-fc48-4447-b380-07ec75e3675a

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_dec

open ActuarialAssurances

theorem solution (n : ℕ) (hn : 0 < n) : dec n (n-1)=1 := by
  simp [dec, Nat.sub_sub_self hn]


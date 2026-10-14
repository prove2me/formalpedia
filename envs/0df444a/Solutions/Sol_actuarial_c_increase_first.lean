-- Prove2me | solution 1 for actuarial_c_increase_first
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:35.589575+00:00
-- url     : https://prove2.me/submissions/a9374185-4a42-40a5-b08d-adddc2db752c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_inc

open ActuarialAssurances

theorem solution  : inc 0=1 := by
  simp [inc]

-- Prove2me | solution 1 for actuarial_c_alive_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:33.690833+00:00
-- url     : https://prove2.me/submissions/4bb267b5-04fa-44e6-a0f3-988f6ee1869f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive

open ActuarialAssurances

theorem solution (k : ℕ) : alive k 0=1 := by
  simp [alive]

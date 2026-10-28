-- Prove2me | solution 1 for actuarial_f_annual_floor_at_least_second
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:35:53.575447+00:00
-- url     : https://prove2.me/submissions/1998358f-5cbd-45f6-868a-c12b74d14f00

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_annualFloorPayment

open ActuarialUnderpinsF

theorem solution (a b ga gb : ℕ → ℝ)
    (z t : ℕ) : b z * gb t ≤ annualFloorPayment a b ga gb z t := by
  exact le_max_right _ _

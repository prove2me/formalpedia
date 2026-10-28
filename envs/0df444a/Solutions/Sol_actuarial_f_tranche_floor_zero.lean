-- Prove2me | solution 1 for actuarial_f_tranche_floor_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:39:10.188442+00:00
-- url     : https://prove2.me/submissions/514f3c88-aedd-4c44-9d82-75a4ffee6620

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_trancheFloorTotal

open ActuarialUnderpinsF

theorem solution (a b : ℕ → ℝ) :
    trancheFloorTotal a b 0 = 0 := by
  simp [trancheFloorTotal]

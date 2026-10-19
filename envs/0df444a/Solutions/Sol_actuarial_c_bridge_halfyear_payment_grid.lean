-- Prove2me | solution 1 for actuarial_c_bridge_halfyear_payment_grid
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T14:49:46.41021+00:00
-- url     : https://prove2.me/submissions/c85c729f-d5a9-4105-b362-8035de07af5d

import Mathlib
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_c_cont_fractionalTime



theorem solution :
    ActuarialAssurances.Continuous.fractionalTime 2 1 = (1 / 2 : ℝ) := by
  simp [ActuarialAssurances.Continuous.fractionalTime, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc]


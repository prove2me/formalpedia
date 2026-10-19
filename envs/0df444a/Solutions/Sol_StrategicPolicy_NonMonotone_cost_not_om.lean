-- Prove2me | solution 1 for StrategicPolicy.NonMonotone.cost_not_om
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-18T01:59:22.475975+00:00
-- url     : https://prove2.me/submissions/1eb72704-a248-436f-8482-cd38a7d2e9fc

import Mathlib
import Definitions.Def_StrategicPolicy_NonMonotone_Setting
import Definitions.Def_StrategicPolicy_NonMonotone_Example

set_option autoImplicit false

namespace StrategicPolicy.NonMonotone.Sol_StrategicPolicy_NonMonotone_cost_not_om

open StrategicPolicy.NonMonotone

theorem q_one_lt_q_zero : StrategicPolicy.NonMonotone.q 1 < StrategicPolicy.NonMonotone.q 0 := by
  simp [StrategicPolicy.NonMonotone.q]
  norm_num

theorem c_zero_one : StrategicPolicy.NonMonotone.c 0 1 = 1 / 5 := by
  simp [StrategicPolicy.NonMonotone.c]

end StrategicPolicy.NonMonotone.Sol_StrategicPolicy_NonMonotone_cost_not_om

open StrategicPolicy.NonMonotone in
theorem solution : ¬ StrategicPolicy.StochasticOpt.OMCost StrategicPolicy.NonMonotone.q
    StrategicPolicy.NonMonotone.c := by
  rintro ⟨-, -, h3⟩
  have h := (h3 0 1 (by decide)).1
    StrategicPolicy.NonMonotone.Sol_StrategicPolicy_NonMonotone_cost_not_om.q_one_lt_q_zero
  rw [StrategicPolicy.NonMonotone.Sol_StrategicPolicy_NonMonotone_cost_not_om.c_zero_one] at h
  norm_num at h

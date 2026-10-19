-- Prove2me | solution 1 for actuarial_e_spouse_immediate_on_settlement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:31:33.889852+00:00
-- url     : https://prove2.me/submissions/6160960b-2e72-45f4-87e9-aac64cf63849

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_spouseDueImmediate

open ActuarialDeathE



theorem solution (i j : ℕ) (hj : i < j) : spouseDueImmediate i j (i + 1) = 1 := by
  unfold spouseDueImmediate ActuarialJointD.onlyY ActuarialJointD.dead ActuarialJointD.alive
  rw [if_neg (by omega), if_pos (by omega)]
  norm_num


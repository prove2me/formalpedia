-- Prove2me | solution 1 for actuarial_e_immediate_deferred_spouse_difference
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:31:43.924992+00:00
-- url     : https://prove2.me/submissions/129e9ef6-7fa2-4259-b562-50acf6211917

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_spouseDue
import Definitions.Def_actuarial_e_spouseDueImmediate

open ActuarialDeathE



theorem solution (i j t : ℕ) : spouseDueImmediate i j t = spouseDue i j t + (if i < j ∧ t = i + 1 then (1 : ℝ) else 0) := by
  unfold spouseDueImmediate spouseDue ActuarialJointD.onlyY ActuarialJointD.dead ActuarialJointD.alive
  split_ifs <;> first | omega | norm_num | (exfalso; omega)


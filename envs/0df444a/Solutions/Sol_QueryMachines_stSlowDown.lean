-- Prove2me | solution 1 for QueryMachines.stSlowDown
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:51:50.5562+00:00
-- url     : https://prove2.me/submissions/82d00344-ed88-4054-9f1c-64fd6e56db10

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Kernel
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Tactic
import Definitions.Def_QueryMachines_Runs
import Theorems.Thm_QueryMachines_QueryMachine_sum_map_unitCost
import Theorems.Thm_QueryMachines_QueryMachine_sum_map_const

set_option autoImplicit false
section
section
open QueryMachines
open Groundwork QueryMachine
namespace QueryMachines
theorem _root_.solution : StSlowDown := fun _ _ _ _ _ _ _ T _ t _ ht ⟨own, L, hr, hle⟩ => ⟨own, L, hr, by
  rw [sum_map_unitCost] at hle
  rw [sum_map_const]
  calc own + L.length * t ≤ own * t + L.length * t := Nat.add_le_add_right (Nat.le_mul_of_pos_right _ ht) _
    _ = (own + L.length) * t := (Nat.add_mul _ _ _).symm
    _ ≤ T * t := Nat.mul_le_mul_right _ hle⟩
end QueryMachines

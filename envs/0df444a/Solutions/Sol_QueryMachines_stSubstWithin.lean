-- Prove2me | solution 1 for QueryMachines.stSubstWithin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:04:48.967603+00:00
-- url     : https://prove2.me/submissions/ae329130-5be1-4ae1-87f8-8837f685baf4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Kernel
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Tactic
import Definitions.Def_QueryMachines_Runs
import Theorems.Thm_QueryMachines_QueryMachine_subst_reaches_within

set_option autoImplicit false
section
section
open QueryMachines
open Groundwork QueryMachine
namespace QueryMachines
theorem _root_.solution : StSubstWithin := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨_, L, hr, hle⟩ hN hw => by
  obtain ⟨own₂, L₂, h2, hle₂⟩ := subst_reaches_within hr hN
  exact ⟨own₂, L₂, h2, by
    have := List.sum_le_sum (l := L) fun x _ => hw x
    omega⟩
end QueryMachines

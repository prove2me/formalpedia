-- Prove2me | solution 1 for QueryMachines.Tower.Toy.oracle_call
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:13:51.8414+00:00
-- url     : https://prove2.me/submissions/04b0c194-3895-44e2-9687-88a3b1cbed86

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Toy_Defs
import Definitions.Def_Tower_Toy_Spec
import Definitions.Def_Tower_Kernel
import Definitions.Def_Tower_TowerRuns
import Definitions.Def_StepMachines_Prog_SideBasics
import Mathlib.Tactic.Ring
import Definitions.Def_Tower_Toy_Meets
import Theorems.Thm_QueryMachines_Tower_Toy_val_child


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower QueryMachines.Tower.Toy
open Groundwork Groundwork.Prog
namespace QueryMachines.Tower.Toy
theorem _root_.solution (ℓ0 M0 l : ℕ) (b b' : Bool) (f : List Bool → Option ℕ) : (spec ℓ0 M0).oracle noG (l + 1, b) f (Sum.inl (l, b')) = some (sumF l fun q => f (b' :: q)) := by
  rw [← val_child ℓ0 M0]; exact if_pos rfl
end QueryMachines.Tower.Toy

-- Prove2me | solution 1 for QueryMachines.Tower.Toy.cost_toy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:01:08.915981+00:00
-- url     : https://prove2.me/submissions/a4f209c0-18ac-4864-aa52-7e577590842e

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

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower QueryMachines.Tower.Toy
open Groundwork Groundwork.Prog
namespace QueryMachines.Tower.Toy
theorem _root_.solution : ∀ l t : ℕ, cost TS TI l t + 5 = 2 ^ l * (t + 2 * l + 5)
  | 0, t => by show t + 5 = _; ring
  | l + 1, t => by
    have ih := solution l (t + 2)
    have e : 2 ^ (l + 1) * (t + 2 * (l + 1) + 5) = 2 * (2 ^ l * (t + 2 + 2 * l + 5)) := by ring
    rw [e, ← ih]
    show 2 * (cost TS TI l (t + 2) + 2) + 1 + 5 = _
    omega
end QueryMachines.Tower.Toy

-- Prove2me | solution 1 for QueryMachines.QueryMachine.orbit_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:06:40.188032+00:00
-- url     : https://prove2.me/submissions/44a760b4-889c-46b7-9397-0930c3a526e3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork Finset
variable {Q Q' A α α₁ α₂ β γ τ : Type}
namespace QueryMachines.QueryMachine
theorem _root_.solution (N : α → ℕ) (a : α) (k y : ℕ) (h : y + k = N a) :
    Stepped.Orbit (Stepped.rangeNext N) (if y < N a then some (a, y) else none) ((List.range' y k).map fun y => (a, y)) := by
  induction k generalizing y with
  | zero => rw [if_neg (by omega)]; exact .nil
  | succ k ih =>
    rw [if_pos (by omega), List.range'_succ, List.map_cons]
    exact .cons (ih (y + 1) (by omega))
end QueryMachines.QueryMachine

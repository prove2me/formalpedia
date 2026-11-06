-- Prove2me | solution 1 for Suffices.tested_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:44:57.768222+00:00
-- url     : https://prove2.me/submissions/209adb86-deee-49c0-b7d3-c5b44889525b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Suffices_Defs
import Definitions.Def_Exits_Tested
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Sat
import Mathlib.Tactic.Ring
import Definitions.Def_Suffices_Sizes
import Theorems.Thm_Exits_tested_cons_of_fail
import Theorems.Thm_Exits_tested_cons_of_pass
import Theorems.Thm_Exits_tested_nil
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open Suffices
open Groundwork Groundwork.Prog CountKSat Exits
namespace Suffices
theorem _root_.solution {μ ν : Type} (f : μ → ν) (u : ν → Bool) (l : List μ) : tested u (l.map f) = (tested (fun x => u (f x)) l).map f := by
  induction l with
  | nil => rw [List.map_nil, tested_nil, tested_nil, List.map_nil]
  | cons x l ih =>
    cases hx : u (f x) with
    | true => rw [List.map_cons, tested_cons_of_pass hx, tested_cons_of_pass (v := fun x => u (f x)) (x := x) hx]; rfl
    | false => rw [List.map_cons, tested_cons_of_fail hx, tested_cons_of_fail (v := fun x => u (f x)) (x := x) hx, List.map_cons, ih]
end Suffices

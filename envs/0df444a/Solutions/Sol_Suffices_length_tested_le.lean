-- Prove2me | solution 1 for Suffices.length_tested_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:49:53.04598+00:00
-- url     : https://prove2.me/submissions/adcbf969-5cbf-4a66-a672-d62bedb15cd6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Suffices_Defs
import Definitions.Def_Exits_Tested
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Sat
import Mathlib.Tactic.Ring
import Definitions.Def_Suffices_Sizes
import Theorems.Thm_Groundwork_DecodeK_IsKCNF_length_le
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Sat3_Is3CNF_length_le
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Suffices
open Groundwork Groundwork.Prog CountKSat Exits
namespace Suffices
theorem _root_.solution {ν : Type} (u : ν → Bool) (l : List ν) : (tested u l).length ≤ l.length := (List.take_sublist _ _).length_le
end Suffices

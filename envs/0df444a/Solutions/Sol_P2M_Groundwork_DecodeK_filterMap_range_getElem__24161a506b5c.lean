-- Prove2me | solution 1 for P2M_Groundwork_DecodeK_filterMap_range_getElem__24161a506b5c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:26:34.765205+00:00
-- url     : https://prove2.me/submissions/28ccd090-ac77-40a7-b82d-f29ad71a6dfd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatStatement
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_WidthK_Decode
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
open Groundwork Groundwork.DecodeK
open Sat3 (Lit CNF Satisfiable slot)
open SatK
open Groundwork.Decode
namespace Groundwork.DecodeK
theorem _root_.solution {α : Type} (l : List α) (k : ℕ) : (List.range k).filterMap (fun j => l[j]?) = l.take k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.filterMap_append, ih, List.take_add_one]
    congr 1
end Groundwork.DecodeK

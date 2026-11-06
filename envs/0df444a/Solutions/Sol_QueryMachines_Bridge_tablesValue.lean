-- Prove2me | solution 1 for QueryMachines.Bridge.tablesValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:32:34.061128+00:00
-- url     : https://prove2.me/submissions/c0f6fdb2-1e59-450f-8582-b76eb1aac041

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_Printed_Coding
import Definitions.Def_CountedToPadded_TablesValue
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Printed_stCliqueValue
import Theorems.Thm_Value_stCliqueValue
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge
open Groundwork Groundwork.Prog PaddedDescent.F Eight.SecNetworks Printed
namespace QueryMachines.Bridge
theorem _root_.solution : TablesValue := by
  intro K lam T hK hlam
  refine (Printed.stCliqueValue K lam (fun w z => entry T (w, z)) hK hlam).trans ?_
  show Inst.ZW lam [] (listTables K fun w z => entry T (w, z)) = Inst.ZW (unary lam).length [] (instOf T)
  rw [show (unary lam).length = lam from List.length_replicate]
  rfl
end QueryMachines.Bridge

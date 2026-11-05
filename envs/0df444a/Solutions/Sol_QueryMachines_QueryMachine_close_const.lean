-- Prove2me | solution 1 for QueryMachines.QueryMachine.close_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:16:55.573114+00:00
-- url     : https://prove2.me/submissions/a5c15a97-a391-4d0e-85ed-a058825fddd5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombDefs
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_QueryMachines_Comb
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_Unary_const
attribute [local fun_prop] Groundwork.PolyT.const



set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork
variable {Q A Q' C α α₁ α₂ β γ δ ι τ : Type}
namespace QueryMachines.QueryMachine
theorem _root_.solution [HasSize α] [HasSize β] (b : β) (O : Q → Option A) :
    (const b : QueryMachine Q A α β).close O = Stepped.const b := rfl
end QueryMachines.QueryMachine

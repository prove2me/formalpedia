-- Prove2me | solution 1 for QueryMachines.QueryMachine.close_mapOut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:15:11.466323+00:00
-- url     : https://prove2.me/submissions/7ee277f9-1b21-4551-a747-4854a7eef5e0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombDefs
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_QueryMachines_Comb

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork
variable {Q A Q' C α α₁ α₂ β γ δ ι τ : Type}
namespace QueryMachines.QueryMachine
theorem _root_.solution (M : QueryMachine Q A α β) (g : β → γ) (O : Q → Option A) :
    (mapOut M g).close O = Stepped.mapOut (M.close O) g := rfl
end QueryMachines.QueryMachine

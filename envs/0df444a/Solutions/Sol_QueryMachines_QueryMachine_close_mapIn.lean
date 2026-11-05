-- Prove2me | solution 1 for QueryMachines.QueryMachine.close_mapIn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:14:36.526713+00:00
-- url     : https://prove2.me/submissions/eaef08e1-5b56-49c4-bfde-5c5ff7369b89

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
theorem _root_.solution (g : α → β) (M : QueryMachine Q A β γ) (O : Q → Option A) :
    (mapIn g M).close O = Stepped.mapIn g (M.close O) := rfl
end QueryMachines.QueryMachine

-- Prove2me | solution 1 for QueryMachines.QueryMachine.close_query
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:14:59.328899+00:00
-- url     : https://prove2.me/submissions/acc6f3a0-0d21-4063-b3d1-7bbbd79c0e13

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombDefs
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_QueryMachines_Comb
import Theorems.Thm_QueryMachines_QueryMachine_stepped_eq


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork
variable {Q A Q' C α α₁ α₂ β γ δ ι τ : Type}
namespace QueryMachines.QueryMachine
theorem _root_.solution [HasSize α] [HasSize A] (h : α → Q) (O : Q → Option A) :
    (query h : QueryMachine Q A α A).close O = Stepped.ofOption fun a => O (h a) :=
  stepped_eq (fun _ => rfl) (fun s => by rcases s with a | b <;> rfl) (fun s => by rcases s with a | b <;> rfl)
end QueryMachines.QueryMachine

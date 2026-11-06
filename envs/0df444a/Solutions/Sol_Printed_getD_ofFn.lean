-- Prove2me | solution 1 for Printed.getD_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:11:26.637752+00:00
-- url     : https://prove2.me/submissions/8e82e59c-bd30-4bb2-a9c3-348d34cc783b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Achievable
import Definitions.Def_Eight_ViaGrouping_Display
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingEntry

set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine
namespace Printed
theorem _root_.solution {α : Type} {g : ℕ} (f : Fin g → α) (a : Fin g) (d : α) : (List.ofFn f).getD a.val d = f a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos a.2]
  rfl
end Printed

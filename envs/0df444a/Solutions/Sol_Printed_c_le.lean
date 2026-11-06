-- Prove2me | solution 1 for Printed.c_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:03:28.23431+00:00
-- url     : https://prove2.me/submissions/f79734a4-3680-4b47-8eff-359e5d1bbd87

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Achievable
import Definitions.Def_Eight_ViaGrouping_Display
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingEntry
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine
namespace Printed
theorem _root_.solution {g : ℕ} {N : Net g} {P B : ℕ} (h : N.Is P B) {a b : Fin g} (hab : a ≠ b) : N.c a b ≤ P :=
  (Finset.single_le_sum (f := fun b => N.c a b) (fun _ _ => Nat.zero_le _) (Finset.mem_erase.2 ⟨hab.symm, mem_univ b⟩)).trans (h.i a)
end Printed

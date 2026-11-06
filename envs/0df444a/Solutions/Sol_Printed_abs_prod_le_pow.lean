-- Prove2me | solution 1 for Printed.abs_prod_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:03:32.323446+00:00
-- url     : https://prove2.me/submissions/0a90f60e-fed0-405d-96be-b3f74f1dfdc5

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
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → ℤ) (m : ℤ) (h : ∀ i ∈ s, |f i| ≤ m) : |∏ i ∈ s, f i| ≤ m ^ #s := by
  rw [Finset.abs_prod, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun i _ => abs_nonneg _) h
end Printed

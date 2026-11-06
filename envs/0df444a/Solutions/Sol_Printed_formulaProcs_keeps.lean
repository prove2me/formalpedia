-- Prove2me | solution 1 for Printed.formulaProcs_keeps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:07:15.964655+00:00
-- url     : https://prove2.me/submissions/b88cb878-622a-4cc3-9515-ad589e1d8cc2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Achievable
import Definitions.Def_Printed_HandOver
import Definitions.Def_Eight_ViaGrouping_Count
import Mathlib.Tactic
import Definitions.Def_Printed_Count
import Theorems.Thm_Eight_ViaGrouping_satProcs_keepsP
import Theorems.Thm_Groundwork_Sparsify_StackOK_mem


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines
namespace Printed
theorem _root_.solution (g k : ℕ) : (formulaProcs g k).Keeps :=
  have h := (satProcs_keepsP g k).keeps
  ⟨h.len, h.cap, h.mem, h.W, h.Ψ, h.f⟩
end Printed

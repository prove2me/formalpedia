-- Prove2me | solution 1 for Printed.stToLists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:23:33.526254+00:00
-- url     : https://prove2.me/submissions/d73d5c34-aa59-4a04-98f6-a9e011645a18

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_CodingDefs
import Definitions.Def_QueryMachines_Comb
import Definitions.Def_Eight_SecNetworks_Clique
import Definitions.Def_Value_Clique
import Mathlib.Tactic
import Definitions.Def_Printed_Coding
import Theorems.Thm_Printed_flatten_copies
import Theorems.Thm_Printed_toLists_eq
import Theorems.Thm_Eight_SecNetworks_length_copyAt
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines
variable {K lam : ℕ}
namespace Printed
theorem _root_.solution : StToLists := fun K lam w z hz =>
  ⟨toLists_eq lam w z, fun u hu => length_copyAt w u hu (mem_words.1 hz), by
    rw [toLists_eq]
    exact Prod.ext rfl (flatten_copies w (mem_words.1 hz))⟩
end Printed

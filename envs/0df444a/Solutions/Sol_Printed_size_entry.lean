-- Prove2me | solution 1 for Printed.size_entry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:48:00.690496+00:00
-- url     : https://prove2.me/submissions/eaae4a43-9d8f-4440-b709-ad2d9a05eb29

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_CodingDefs
import Definitions.Def_QueryMachines_Comb
import Definitions.Def_Eight_SecNetworks_Clique
import Definitions.Def_Value_Clique
import Mathlib.Tactic
import Definitions.Def_Printed_Coding
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_Groundwork_size_int
attribute [local simp] Groundwork.size_int



set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines
variable {K lam : ℕ}
namespace Printed
theorem _root_.solution {v : ℤ} {B : ℕ} (h : |v| < 2 ^ B) : size v ≤ B + 1 := by
  rw [size_int]
  have h1 : v.natAbs < 2 ^ B := by
    have : ((v.natAbs : ℕ) : ℤ) < ((2 ^ B : ℕ) : ℤ) := by rw [Int.natCast_natAbs]; exact_mod_cast h
    exact_mod_cast this
  have := Nat.size_le.2 h1
  omega
end Printed

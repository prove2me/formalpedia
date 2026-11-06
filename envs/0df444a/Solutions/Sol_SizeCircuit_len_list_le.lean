-- Prove2me | solution 1 for SizeCircuit.len_list_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:44:14.679363+00:00
-- url     : https://prove2.me/submissions/5c1cabd2-8af6-4471-91be-aba2a9001f88

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Definitions.Def_SizeCircuit_Addition
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_List3
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Cert
import Theorems.Thm_P2M_SizeCircuit_len_list_le__68fc5a2a8b09
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks
namespace SizeCircuit
theorem _root_.solution {α : Type} [Enc α] {B L : ℕ} {l : List α} (h : ∀ a ∈ l, len a ≤ B) (hL : l.length ≤ L) : len l ≤ L * (B + 2) + 2 :=
  (len_list_le' l h).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hL) 2)
end SizeCircuit

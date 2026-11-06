-- Prove2me | solution 1 for SizeCircuit.len_nat_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:32:14.024413+00:00
-- url     : https://prove2.me/submissions/53a441a4-2739-4d01-8d34-ab9bd35f375c

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
import Theorems.Thm_Groundwork_RebalanceArith_size_le


set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks
namespace SizeCircuit
theorem _root_.solution {x M : ℕ} (h : x ≤ M) : len x ≤ 3 * M + 2 := by
  have h1 : Nat.size x ≤ x := Nat.size_le.2 Nat.lt_two_pow_self
  rw [len_nat]
  omega
end SizeCircuit

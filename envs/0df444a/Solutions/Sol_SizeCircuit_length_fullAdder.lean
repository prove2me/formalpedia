-- Prove2me | solution 1 for SizeCircuit.length_fullAdder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:29:41.49221+00:00
-- url     : https://prove2.me/submissions/d15f3aff-706a-4d4b-9237-d4221fe470ec

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Addition
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks
namespace SizeCircuit
theorem _root_.solution (N a u w : ℕ) : (fullAdder N a u w).length = 5 := rfl
end SizeCircuit

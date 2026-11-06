-- Prove2me | solution 1 for SizeCircuit.addStep_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:53:07.72888+00:00
-- url     : https://prove2.me/submissions/b7b19e48-9a86-4b51-9125-e9d9e14af858

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
theorem _root_.solution (n a u w : ℕ) (r nxt dig : List ℕ) (K : List GateD) : addStep n (a :: u :: w :: r, nxt, dig, K) =
    ((n + K.length + 1) :: r, (n + K.length + 4) :: nxt, dig, K ++ fullAdder (n + K.length) a u w) := rfl
end SizeCircuit

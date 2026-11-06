-- Prove2me | solution 1 for SizeCircuit.addValue_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:51:37.404777+00:00
-- url     : https://prove2.me/submissions/34b545f8-6b03-49e7-b4cd-7cb212f100f9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Addition
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks
namespace SizeCircuit
theorem _root_.solution (v : ℕ → Bool) (cur nxt dig : List ℕ) (K : List GateD) :
    addValue v (cur, nxt, dig, K) = ofWord (dig.map v) + 2 ^ dig.length * (onesAmong v cur + 2 * onesAmong v nxt) := rfl
end SizeCircuit

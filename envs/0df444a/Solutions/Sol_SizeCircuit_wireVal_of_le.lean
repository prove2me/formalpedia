-- Prove2me | solution 1 for SizeCircuit.wireVal_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:18:27.61866+00:00
-- url     : https://prove2.me/submissions/8cc166f3-0da8-40ed-bb78-0076e42b388e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_CircuitLowerBound_Circ_Form
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_General
import Theorems.Thm_CircuitLowerBound_Form_length_wires
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat CircuitLowerBound CircuitLowerBound.Blocks ENP
namespace SizeCircuit
theorem _root_.solution (x : List Bool) (K : List GateD) {i : ℕ} (hi : x.length + K.length ≤ i) : wireVal x K i = false := by
  refine List.getD_eq_default _ _ ?_
  rw [Form.length_wires, toC, List.length_map]
  exact hi
end SizeCircuit

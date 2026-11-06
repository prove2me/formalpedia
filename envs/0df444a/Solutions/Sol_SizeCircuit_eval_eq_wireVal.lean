-- Prove2me | solution 1 for SizeCircuit.eval_eq_wireVal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:18:53.924092+00:00
-- url     : https://prove2.me/submissions/2523612c-273c-47af-bae8-8743a2f90efa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_CircuitLowerBound_Circ_Form
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_General
import Theorems.Thm_CircuitLowerBound_Form_eval_eq
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat CircuitLowerBound CircuitLowerBound.Blocks ENP
namespace SizeCircuit
theorem _root_.solution (x : List Bool) (K : List GateD) : eval (toC K) x = wireVal x K (x.length + K.length - 1) := by
  rw [Form.eval_eq, toC, List.length_map]
  rfl
end SizeCircuit

-- Prove2me | solution 1 for SizeCircuit.lt_of_wfa
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:27:44.140796+00:00
-- url     : https://prove2.me/submissions/9a778f8b-5b74-40a2-9208-c09737486362

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks
namespace SizeCircuit
theorem _root_.solution : ∀ {K : List GateD} {n : ℕ}, WFa n K → ∀ g ∈ K, g.2.1 < n + K.length ∧ g.2.2 < n + K.length
  | [], _, _, g, hg => absurd hg List.not_mem_nil
  | g' :: K, n, h, g, hg => by
    rw [List.length_cons]
    rcases List.mem_cons.1 hg with e | hg
    · have := h.1
      rw [e]
      omega
    · have := solution h.2 g hg
      omega
end SizeCircuit

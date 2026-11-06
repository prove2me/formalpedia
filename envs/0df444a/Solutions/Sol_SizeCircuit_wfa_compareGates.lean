-- Prove2me | solution 1 for SizeCircuit.wfa_compareGates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:25:08.57999+00:00
-- url     : https://prove2.me/submissions/70f00f07-6e02-4aca-9800-c963aeb476b3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Compare
import Theorems.Thm_CircuitLowerBound_Blocks_wfa_map
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks
namespace SizeCircuit
theorem _root_.solution {N s : ℕ} {digits : List ℕ} (hN : 0 < N) (hd : ∀ x ∈ digits, x < N) : WFa N (compareGates N s digits) := by
  refine ⟨⟨hN, hN⟩, (wfa_map (N + 1) _ digits.length).2 fun i hi => ⟨?_, ?_⟩⟩
  · show N + i < N + 1 + i
    omega
  · show digits.getD i 0 < N + 1 + i
    rw [List.getD_eq_getElem _ _ hi]
    have := hd _ (List.getElem_mem hi)
    omega
end SizeCircuit

-- Prove2me | solution 1 for SizeCircuit.testBit_num
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:27:25.74757+00:00
-- url     : https://prove2.me/submissions/48527ff5-c4f4-4f9d-81e6-7132e3ca71df

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Compare
import Theorems.Thm_CircuitLowerBound_Blocks_getD_toWord
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_testBit
import Theorems.Thm_Groundwork_toWord_ofWord
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.testBit



set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks
namespace SizeCircuit
theorem _root_.solution (b : ℕ → Bool) (L i : ℕ) (hi : i < L) : (num b L).testBit i = b i := by
  have h1 : toWord L (num b L) = (List.range L).map b := by
    have h := toWord_ofWord ((List.range L).map b)
    rw [List.length_map, List.length_range] at h
    exact h
  rw [← getD_toWord hi, h1, List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hi), List.getElem_map, List.getElem_range]
end SizeCircuit

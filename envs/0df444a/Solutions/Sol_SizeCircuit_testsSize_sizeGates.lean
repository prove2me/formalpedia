-- Prove2me | solution 1 for SizeCircuit.testsSize_sizeGates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:25:11.164615+00:00
-- url     : https://prove2.me/submissions/6ce2d7fb-864a-4b60-ae99-0561bf888475

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Definitions.Def_SizeCircuit_General
import Definitions.Def_SizeCircuit_Addition
import Definitions.Def_SizeCircuit_Compare
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Circuit
import Theorems.Thm_SizeCircuit_onesAmong_inputs
import Theorems.Thm_CircuitLowerBound_Blocks_obeys_append
import Theorems.Thm_CircuitLowerBound_Blocks_wf_of_wfa
import Theorems.Thm_CircuitLowerBound_Blocks_wfa_append
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_SizeCircuit_addValue_added
import Theorems.Thm_SizeCircuit_added_spec
import Theorems.Thm_SizeCircuit_compareGates_spec
import Theorems.Thm_SizeCircuit_eval_eq_wireVal
import Theorems.Thm_SizeCircuit_length_compareGates
import Theorems.Thm_SizeCircuit_obeys_wireVal
import Theorems.Thm_SizeCircuit_wfa_compareGates
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks ENP
namespace SizeCircuit
theorem _root_.solution : TestsSize sizeGates 6 := by
  intro n s hn
  obtain ⟨-, -, hd, hW, hK, hD⟩ := added_spec n
  have hlen : (sizeGates n s).length = (added n).2.2.2.length + ((added n).2.2.1.length + 1) := by
    rw [sizeGates, List.length_append, length_compareGates]
  have hWF : WFa n (sizeGates n s) := (wfa_append n _ _).2 ⟨hW, wfa_compareGates (by omega) hd⟩
  refine ⟨fun h => ?_, by rw [hlen]; omega, wf_of_wfa hWF, fun x hx => ?_⟩
  · rw [h, List.length_nil] at hlen
    omega
  · subst hx
    have hO : Obeys (wireVal x (sizeGates x.length s)) x.length
        ((added x.length).2.2.2 ++ compareGates (x.length + (added x.length).2.2.2.length) s (added x.length).2.2.1) :=
      obeys_wireVal x (sizeGates x.length s) hWF
    obtain ⟨h1, h2⟩ := (obeys_append _ _ _ _).1 hO
    have e1 := addValue_added _ _ h1
    have e2 := compareGates_spec _ _ _ _ h2
    have hidx : x.length + (sizeGates x.length s).length - 1 = x.length + (added x.length).2.2.2.length + (added x.length).2.2.1.length := by
      rw [hlen]
      omega
    rw [eval_eq_wireVal, hidx, e2, e1, onesAmong_inputs, decide_eq_true_eq]
end SizeCircuit

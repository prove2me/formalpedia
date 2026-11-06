-- Prove2me | solution 1 for SizeCircuit.stGamma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:07:55.552417+00:00
-- url     : https://prove2.me/submissions/93531e1b-2ea2-4dd9-85de-65caa066de56

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_SizeCircuit_General
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Gamma
import Theorems.Thm_SizeCircuit_length_formulaOf
import Theorems.Thm_SizeCircuit_shaped_formulaOf
import Theorems.Thm_SizeCircuit_holds_formulaOf
import Theorems.Thm_SizeCircuit_count_ofFn
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_SizeCircuit_stUniqueExtension
import Theorems.Thm_SizeCircuit_wfa_of_wf
attribute [local fun_prop] Groundwork.PolyT.filter



set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound CircuitLowerBound.Blocks ENP
namespace SizeCircuit
theorem _root_.solution : StGamma := by
  intro gates a hT n s hn
  obtain ⟨hne, hlen, hWF, hev⟩ := hT n s hn
  refine ⟨shaped_formulaOf (wfa_of_wf hWF) hne, ?_, ?_, fun x => ?_⟩
  · rw [Nat.succ_mul]
    omega
  · rw [length_formulaOf, Nat.mul_assoc]
    omega
  · obtain ⟨⟨b0, ⟨hb0, hH0⟩, hu⟩, hout⟩ := stUniqueExtension n (gates n s) hWF hne x
    have hc : ENP.eval (toC (gates n s)) (List.ofFn x) = true ↔ (Finset.univ.filter fun i => x i = true).card = s := by
      rw [hev (List.ofFn x) List.length_ofFn, count_ofFn]
    refine ⟨fun hs => ⟨b0, ⟨hb0, (holds_formulaOf _ _ _).2 ⟨hH0, ?_⟩⟩, ?_⟩, ?_⟩
    · rw [hout b0 hb0 hH0]
      exact hc.2 hs
    · rintro b ⟨hb, hH⟩
      exact hu b ⟨hb, ((holds_formulaOf _ _ _).1 hH).1⟩
    · rintro hs ⟨b, hb, hH⟩
      obtain ⟨h1, h2⟩ := (holds_formulaOf _ _ _).1 hH
      rw [hout b hb h1] at h2
      exact hs (hc.1 h2)
end SizeCircuit

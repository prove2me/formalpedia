-- Prove2me | solution 1 for SizeCircuit.stUniqueExtension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:35:17.206194+00:00
-- url     : https://prove2.me/submissions/b076baa4-1be8-4bb9-aac6-2b71880183da

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_CircuitLowerBound_Circ_Form
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_General
import Theorems.Thm_SizeCircuit_holds_wiresFormula
import Theorems.Thm_SizeCircuit_wfa_of_wf
import Theorems.Thm_SizeCircuit_obeys_unique
import Theorems.Thm_SizeCircuit_obeys_wireVal
import Theorems.Thm_SizeCircuit_wireVal_input
import Theorems.Thm_SizeCircuit_eval_eq_wireVal
import Theorems.Thm_SizeCircuit_wireVal_of_le
import Theorems.Thm_SizeCircuit_ext_of_lt
import Theorems.Thm_SizeCircuit_ext_of_le
import Theorems.Thm_CountKSat_Value_ext_of_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat CircuitLowerBound CircuitLowerBound.Blocks ENP
namespace SizeCircuit
theorem _root_.solution : StUniqueExtension := by
  intro n K hK hne x
  have hW : WFa n K := wfa_of_wf hK
  have hXl : (List.ofFn x).length = n := List.length_ofFn
  have hOb : Obeys (wireVal (List.ofFn x) K) n K := by
    have h := obeys_wireVal (List.ofFn x) K (by rw [hXl]; exact hW)
    rwa [hXl] at h
  have hin : ∀ i : Fin n, wireVal (List.ofFn x) K i.1 = x i := by
    intro i
    rw [wireVal_input _ _ (by rw [hXl]; exact i.2), List.getD_eq_getElem _ _ (by rw [hXl]; exact i.2), List.getElem_ofFn]
  have key : ∀ b : Fin (n + K.length) → Bool, (∀ i : Fin n, b (Fin.castAdd K.length i) = x i) → Holds (ext b) (wiresFormula n K) →
      ∀ i < n + K.length, ext b i = wireVal (List.ofFn x) K i := by
    intro b hb hH
    refine obeys_unique hW ((holds_wiresFormula _ n K).1 hH) hOb fun i hi => ?_
    rw [ext_of_lt b (by omega : i < n + K.length)]
    exact (hb ⟨i, hi⟩).trans (hin ⟨i, hi⟩).symm
  have hext : ext (fun i : Fin (n + K.length) => wireVal (List.ofFn x) K i.1) = wireVal (List.ofFn x) K := by
    funext i
    rcases Nat.lt_or_ge i (n + K.length) with h | h
    · rw [ext_of_lt _ h]
    · rw [ext_of_le _ h, wireVal_of_le _ _ (by rw [hXl]; exact h)]
  refine ⟨⟨fun i => wireVal (List.ofFn x) K i.1, ⟨fun i => hin i, ?_⟩, ?_⟩, ?_⟩
  · rw [hext]
    exact (holds_wiresFormula _ n K).2 hOb
  · rintro b ⟨hb, hH⟩
    funext i
    have h := key b hb hH i.1 i.2
    rwa [ext_of_lt b i.2] at h
  · intro b hb hH
    have hp : 0 < K.length := List.length_pos_iff.2 hne
    rw [key b hb hH _ (by omega), eval_eq_wireVal, hXl]
end SizeCircuit

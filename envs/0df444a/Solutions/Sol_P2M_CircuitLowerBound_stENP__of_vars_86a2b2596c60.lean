-- Prove2me | solution 1 for P2M_CircuitLowerBound_stENP__of_vars_86a2b2596c60
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:24:16.479204+00:00
-- url     : https://prove2.me/submissions/04a8fcd5-553b-4103-9c39-f4c05a471205

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_ENP_Round
import Definitions.Def_CircuitLowerBound_Small
import Definitions.Def_CountKSatRate_Pad
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_ENP_Restart
import Theorems.Thm_CircuitLowerBound_Restart_length_greedy
import Theorems.Thm_CircuitLowerBound_Restart_time_le
import Theorems.Thm_CircuitLowerBound_Restart_protocol
import Theorems.Thm_CircuitLowerBound_Round_eW_polyT
import Theorems.Thm_CircuitLowerBound_Round_eW_roundInput
import Theorems.Thm_CircuitLowerBound_Round_length_roundInput
import Theorems.Thm_CircuitLowerBound_Round_roundF_polyT
import Theorems.Thm_CircuitLowerBound_Round_roundF_roundInput
import Theorems.Thm_CircuitLowerBound_SmallFacts_length_greedy
import Theorems.Thm_CountKSatRate_stPaddedW
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_ofWord_lt
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork PaddedDescent Turing
open Restart
namespace CircuitLowerBound
theorem _root_.solution (h1 : StCertSched) (h2 : StCertTabF) (h3 : StFlip) (h4 : StVars) : StENP' := by
  obtain ⟨G, hG, hGs⟩ := h2
  obtain ⟨fb, hfb, hfbs⟩ := h3
  obtain ⟨N, q, hfin, hN⟩ := CountKSatRate.stPaddedW eW (roundF G fb) Round.eW_polyT (Round.roundF_polyT h1 hG hfb)
  refine ⟨N, 6 * q + 1, hfin, fun x => ⟨(greedy (Phi x.length) (ofWord x + 1)).getD (ofWord x) false, Iff.rfl, ?_⟩⟩
  have hi : ofWord x < 2 ^ x.length := ofWord_lt x
  -- what a round returns, and its time
  have hR : ∀ ans : List Bool, ans.length ≤ 2 ^ x.length → ENP.Round N (2 ^ ((6 * q + 1) * (x.length + 1))) x ans
      (bif decide (ans.length ≤ ofWord x) then true :: encCnf (Phi x.length ++ units (ans.map (fun b => !b) ++ [false]))
        else [false, !ans.getD (ofWord x) false]) := by
    intro ans ha
    have h := hN (roundInput x ans)
    rw [Round.eW_roundInput, Round.roundF_roundInput hGs hfbs h4 x ans ha (by rw [pad, List.length_replicate]), Round.length_roundInput] at h
    obtain ⟨ev⟩ := h
    exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (time_le q x.length ans.length ha)⟩⟩
  have hnn : ∀ l : List Bool, (l.map fun b => !b).map (fun b => !b) = l := by
    intro l
    have e : ((fun b : Bool => !b) ∘ fun b : Bool => !b) = id := funext fun b => Bool.not_not b
    rw [List.map_map, e, List.map_id]
  have hP := protocol (N := N) (T := 2 ^ ((6 * q + 1) * (x.length + 1))) (x := x) (φ := Phi x.length) (fun j hj => ?_) ?_ (ofWord x + 1) 0
    (2 ^ ((6 * q + 1) * (x.length + 1))) (by omega) ?_
  · exact hP
  · have h := hR ((greedy (Phi x.length) j).map fun b => !b) (by rw [List.length_map, length_greedy]; omega)
    rw [List.length_map, length_greedy, decide_eq_true hj, cond_true, hnn] at h
    exact h
  · have h := hR ((greedy (Phi x.length) (ofWord x + 1)).map fun b => !b) (by rw [List.length_map, length_greedy]; omega)
    have hlen : ofWord x < (greedy (Phi x.length) (ofWord x + 1)).length := by rw [length_greedy]; omega
    rw [List.length_map, length_greedy, decide_eq_false (by omega), cond_false,
      List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hlen), List.getElem_map, Bool.not_not, ← List.getD_eq_getElem _ false hlen] at h
    exact h
  · have h5 : 2 ^ x.length ≤ 2 ^ ((6 * q + 1) * (x.length + 1)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    omega
end CircuitLowerBound

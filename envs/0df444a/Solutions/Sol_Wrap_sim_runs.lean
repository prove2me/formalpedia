-- Prove2me | solution 1 for Wrap.sim_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:01:06.341636+00:00
-- url     : https://prove2.me/submissions/35571822-5f9f-48d7-8feb-de378d41f030

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Coding
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Definitions.Def_CountKSat_Host
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_Wrap_Sim
import Theorems.Thm_Wrap_run_sim
import Theorems.Thm_Wrap_size_rep_iterate_le
import Theorems.Thm_CircuitLowerBound_Tab_Enc_step
import Theorems.Thm_CircuitLowerBound_Tab_haltList_stk_self
import Theorems.Thm_CircuitLowerBound_Tab_iterate_stay_of_halted
import Theorems.Thm_CircuitLowerBound_Tab_stay_of_evals
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_runs_of_run
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open Wrap
open Turing Groundwork CircuitLowerBound.Tab
variable {M : TM2ComputableAux Bool Bool}
namespace Wrap
theorem _root_.solution (K : Coding M) (pre post : List Bool → List Bool) {x y : List Bool} {t : ℕ} (h : Outputs M (pre x) y t) :
    (sim K pre post).Runs x t (K.a * ((pre x).length + 1) + K.a * t) (post y) := by
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ = initList M.tm ((pre x).map M.inputAlphabet.invFun) := ⟨_, rfl⟩
  obtain ⟨n, hnt, hev⟩ : ∃ n ≤ t, (flip bind M.tm.step)^[n] (some c₀) = some (haltList M.tm (y.map M.outputAlphabet.invFun)) := by
    obtain ⟨ev⟩ := h
    exact ⟨ev.steps, ev.steps_le_m, by rw [hc₀]; exact ev.evals_in_steps⟩
  have hn : (stay M)^[n] c₀ = haltList M.tm (y.map M.outputAlphabet.invFun) := stay_of_evals M n hev
  have h0 : size (K.rep c₀) ≤ K.a * ((pre x).length + 1) := by
    rw [hc₀, ← K.init_rep]
    exact K.size_init _
  have hle : K.a * n ≤ K.a * t := Nat.mul_le_mul_left _ hnt
  have hsize : ∀ j, size (K.rep ((stay M)^[j] c₀)) ≤ K.a * ((pre x).length + 1) + K.a * t := fun j => by
    rcases Nat.le_total j n with hj | hj
    · have h1 := size_rep_iterate_le K c₀ j
      have h2 : K.a * j ≤ K.a * n := Nat.mul_le_mul_left _ hj
      omega
    · have h1 := size_rep_iterate_le K c₀ n
      rw [show j = (j - n) + n from (Nat.sub_add_cancel hj).symm, Function.iterate_add_apply, hn, iterate_stay_of_halted M rfl, ← hn]
      omega
  refine (Stepped.runs_of_run (t := n) ?_ fun j => ?_).mono hnt le_rfl
  · rw [run_sim, ← hc₀, hn]
    change (K.out _).map post = _
    rw [K.out_halted _ rfl, haltList_stk_self, List.map_map]
    have e : (M.outputAlphabet ∘ M.outputAlphabet.invFun) = id := funext fun b => M.outputAlphabet.right_inv b
    rw [e, List.map_id, Option.map_some]
  · rw [run_sim, ← hc₀]
    exact hsize j
end Wrap

-- Prove2me | solution 1 for Sat3Graph.stAskSized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:24:12.866109+00:00
-- url     : https://prove2.me/submissions/dd437af8-68eb-4be0-82c1-631800d0c98c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_Sat3Graph_Split
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_SizeCircuit_Gamma
import Definitions.Def_SizeCircuit_Sized
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Ask
import Theorems.Thm_Sat3Graph_withGamma_replicate
import Theorems.Thm_Eight_Width_numFresh_le
import Theorems.Thm_Groundwork_PolyT_dedup
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Sat3Graph_cntN_of_dedup
import Theorems.Thm_Sat3Graph_exists_bounds
import Theorems.Thm_Sat3Graph_numFresh_append
import Theorems.Thm_Sat3Graph_numFresh_dedup_le
import Theorems.Thm_Sat3Graph_numFresh_eq_zero
import Theorems.Thm_Sat3Graph_sat_iff_cntN
import Theorems.Thm_Sat3Graph_splitN_spec
import Theorems.Thm_SizeCircuit_le_numVars
import Theorems.Thm_SizeCircuit_numVars_le
import Theorems.Thm_SizeCircuit_shaped_gamma
import Theorems.Thm_SizeCircuit_stGammaCount
import Theorems.Thm_SplitSat_widthP_replicate
attribute [local fun_prop] Groundwork.PolyT.dedup



set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight.Width SizeCircuit SplitSat
namespace Sat3Graph
theorem _root_.solution : StAskSized := by
  intro gates a hT w B δ δ₃ _ h0 hle D c hD
  obtain ⟨c', hc'⟩ := exists_bounds (a + 1 + B) c h0 (by push_cast; exact hle)
  refine ⟨c', fun n s ψ _ hψ hB => ?_⟩
  obtain ⟨N0, hN0⟩ : ∃ N0, N0 = numVars gates n s := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = (ψ ++ gamma gates n s).dedup := ⟨_, rfl⟩
  have hnN : n ≤ N0 := hN0 ▸ le_numVars gates n s
  have hvars : ∀ C ∈ φ, ∀ l ∈ C, l.1 < N0 := by
    intro C hC l hl
    rw [hφ] at hC
    rcases List.mem_append.1 (List.mem_dedup.1 hC) with h | h
    · exact lt_of_lt_of_le ((hψ C h).2 l hl) hnN
    · exact hN0 ▸ (shaped_gamma hT n s C h).2 l hl
  have hfresh : numFresh φ ≤ B * (n + 1) := by
    have e1 := numFresh_dedup_le (ψ ++ gamma gates n s)
    have e2 := Eight.Width.numFresh_le w ψ fun C hC => (hψ C hC).1
    have e3 : numFresh (gamma gates n s) = 0 := numFresh_eq_zero fun C hC => (shaped_gamma hT n s C hC).1
    rw [numFresh_append, e3] at e1
    rw [hφ]
    omega
  have hN : N0 + numFresh φ ≤ (a + 1 + B) * (n + 1) := by
    have e := numVars_le hT n s
    rw [← hN0] at e
    rw [Nat.add_mul]
    omega
  obtain ⟨h3, hnd, hsat⟩ := splitN_spec hvars
  obtain ⟨T, b, hr, hb, hTle⟩ := hD (N0 + numFresh φ) (splitN N0 φ) h3 hnd
  have hin : widthP (withGamma gates (List.replicate n (), s, ψ)) = (List.replicate (N0 + numFresh φ) (), splitN N0 φ) := by
    rw [withGamma_replicate, ← hN0, ← hφ, widthP_replicate]
  obtain ⟨k1, k2⟩ := hc' n _ T hN hTle
  rw [← hin] at hr
  refine ⟨T, b, (Stepped.mapIn_runs (f := fun p => widthP (withGamma gates p)) (a := (List.replicate n (), s, ψ)) hr).mono le_rfl k1, ?_, k2⟩
  rw [hb, hsat, sat_iff_cntN hvars, hφ, cntN_of_dedup, hN0, stGammaCount gates a hT n s ψ fun C hC => (hψ C hC).2]
end Sat3Graph

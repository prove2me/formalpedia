-- Prove2me | solution 1 for Sat3Graph.stColoring
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:13:46.374919+00:00
-- url     : https://prove2.me/submissions/9a32bc4d-b54a-46d8-b62a-c86ac7cdd8b0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_Sat3Graph_Split
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_GraphProblems_Color
import Definitions.Def_GraphProblems_Read
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Coloring
import Theorems.Thm_Sat3Graph_numFresh_colorF
import Theorems.Thm_GraphProblems_stAdj
import Theorems.Thm_GraphProblems_stColor
import Theorems.Thm_GraphProblems_stDecideColor
import Theorems.Thm_GraphProblems_stRead1
import Theorems.Thm_GraphProblems_stShapeColor
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_dedup
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_st4_cnt
import Theorems.Thm_Groundwork_TM_st4_src
import Theorems.Thm_Groundwork_TM_st4_t1
import Theorems.Thm_Groundwork_TM_st4_t2
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
import Theorems.Thm_Groundwork_TM_update_withIO
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Sat3Graph_cntN_of_dedup
import Theorems.Thm_Sat3Graph_exists_bounds
import Theorems.Thm_Sat3Graph_numFresh_dedup_le
import Theorems.Thm_Sat3Graph_sat_iff_cntN
import Theorems.Thm_Sat3Graph_splitN_spec
import Theorems.Thm_SplitSat_widthP_replicate
attribute [local fun_prop] Groundwork.PolyT.dedup
attribute [local simp] Groundwork.Host.upd_none
attribute [local simp] Groundwork.Host.withIO_none
attribute [local simp] Groundwork.Host.withIO_some
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.TM.st4_cnt
attribute [local simp] Groundwork.TM.st4_src
attribute [local simp] Groundwork.TM.st4_t1
attribute [local simp] Groundwork.TM.st4_t2
attribute [local simp] Groundwork.TM.st_a
attribute [local simp] Groundwork.TM.st_b
attribute [local simp] Groundwork.TM.st_cnt
attribute [local simp] Groundwork.TM.st_main
attribute [local simp] Groundwork.TM.upd4_cnt
attribute [local simp] Groundwork.TM.upd4_src
attribute [local simp] Groundwork.TM.upd4_t1
attribute [local simp] Groundwork.TM.upd4_t2
attribute [local simp] Groundwork.TM.upd_a
attribute [local simp] Groundwork.TM.upd_b
attribute [local simp] Groundwork.TM.upd_main
attribute [local simp] Groundwork.TM.update_withIO
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit



set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight.Width SplitSat
namespace Sat3Graph
theorem _root_.solution : StColoring := by
  intro k hk δ δ₃ _ h0 hle D c hD
  obtain ⟨c', hc'⟩ := exists_bounds (δ := δ) (2 * k - 3) c h0 (by rw [Nat.cast_sub (by omega)]; push_cast; exact hle)
  refine ⟨c', fun n G => ?_⟩
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = (colorF k n (matrix G)).dedup := ⟨_, rfl⟩
  have hvars : ∀ C ∈ φ, ∀ l ∈ C, l.1 < n * k := by
    intro C hC
    rw [hφ] at hC
    exact (stShapeColor k n _ C (List.mem_dedup.1 hC)).2
  have hfresh : numFresh φ ≤ (k - 3) * n := by
    rw [hφ]
    exact (numFresh_dedup_le _).trans (numFresh_colorF k n _)
  have hN : n * k + numFresh φ ≤ (2 * k - 3) * (n + 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have e1 : 2 * (j + 3) - 3 = 2 * j + 3 := by omega
    have e2 : j + 3 - 3 = j := by omega
    rw [e2] at hfresh
    rw [e1]
    have e3 : (2 * j + 3) * (n + 1) = n * (j + 3) + j * n + (2 * j + 3) := by ring
    omega
  obtain ⟨h3, hnd, hsat⟩ := splitN_spec hvars
  obtain ⟨T, b, hr, hb, hTle⟩ := hD (n * k + numFresh φ) (splitN (n * k) φ) h3 hnd
  have hin : widthP (readC k (code G)) = (List.replicate (n * k + numFresh φ) (), splitN (n * k) φ) := by
    have e : readC k (code G) = (List.replicate (n * k) (), φ) := by
      rw [hφ]
      simp [readC, stRead1 n G]
    rw [e, widthP_replicate]
  obtain ⟨k1, k2⟩ := hc' n _ T hN hTle
  rw [← hin] at hr
  refine ⟨T, b, (Stepped.mapIn_runs (f := fun x => widthP (readC k x)) (a := code G) hr).mono le_rfl k1, ?_, k2⟩
  rw [hb, hsat, sat_iff_cntN hvars, hφ, cntN_of_dedup, stColor stAdj k n G]
  exact (stDecideColor k n G).symm
end Sat3Graph

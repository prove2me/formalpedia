-- Prove2me | solution 1 for PaddedDescent.F.Mark.layersE_eq_layersM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:20:49.45592+00:00
-- url     : https://prove2.me/submissions/ef3f21b1-ad4b-4a81-a397-a8aedfba4516

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_MarkSums
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Definitions.Def_PaddedDescent_F_MarkLayers
import Theorems.Thm_PaddedDescent_F_Mark_Layers_drop_eq_cons
import Theorems.Thm_PaddedDescent_F_Mark_Layers_getLastD_drop
import Theorems.Thm_PaddedDescent_F_Mark_Layers_flatten_drop_sublist
import Theorems.Thm_PaddedDescent_F_Mark_Inv_good
import Theorems.Thm_PaddedDescent_F_Mark_Inv_good_trial
import Theorems.Thm_PaddedDescent_F_Mark_layersM_append
import Theorems.Thm_PaddedDescent_F_Mark_length_layersM
import Theorems.Thm_PaddedDescent_F_Mark_layersM_ne_nil
import Theorems.Thm_PaddedDescent_F_Mark_inv_layersM
import Theorems.Thm_PaddedDescent_F_Mark_last_layersM_le
import Theorems.Thm_PaddedDescent_F_Mark_placeE_eq_placeM
import Theorems.Thm_PaddedDescent_F_Mark_perm_flatten_layersM
import Theorems.Thm_PaddedDescent_F_Mark_layersE_append
import Theorems.Thm_Groundwork_PolyT_length
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
import Theorems.Thm_Sat3_Is3CNF_length_le
attribute [local fun_prop] Groundwork.PolyT.length
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
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark
open Finset Groundwork.Prog
open Layers
namespace PaddedDescent.F.Mark
theorem _root_.solution {n w R : ℕ} {ev : List Fml → ℤ} {ψ : Fml} (hw : n + 2 ≤ w) (hR : 2 ^ R * ψ.length + 5 * 3 ^ R ≤ 3 ^ R * w)
    (hev : ∀ Ls, Asked n w R ψ Ls → ev Ls = trunc n w Ls) : ∀ ψ' : Fml, ψ' <+: ψ → layersE ev w R ψ' = layersM n w R ψ' := by
  intro ψ'
  induction ψ' using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton ψ' C ih =>
    intro hp
    have hp' : ψ' <+: ψ := (List.prefix_append ψ' [C]).trans hp
    have hlen : ψ'.length ≤ ψ.length := hp'.length_le
    have hR' : 2 ^ R * ψ'.length + 5 * 3 ^ R ≤ 3 ^ R * w := le_trans (by gcongr) hR
    have hI := inv_layersM hw R ψ'
    have hl := last_layersM_le hw hR'
    rw [layersE_append, ih hp', layersM_append]
    refine placeE_eq_placeM C (layersM_ne_nil n w R ψ') hI hl fun i hi => ?_
    have hL := length_layersM n w R ψ'
    have hd := drop_eq_cons (show i < (layersM n w R ψ').length by omega)
    have hd' := drop_eq_cons hi
    have hIi : Inv n w ((layersM n w R ψ').getD i [] :: (layersM n w R ψ').getD (i + 1) [] :: (layersM n w R ψ').drop (i + 1 + 1)) := by
      rw [← hd', ← hd]; exact hI.drop i
    have hli : (((layersM n w R ψ').getD i [] :: (layersM n w R ψ').getD (i + 1) [] :: (layersM n w R ψ').drop (i + 1 + 1)).getLastD []).length ≤ w := by
      rw [← hd', ← hd, getLastD_drop (by omega)]; exact hl
    have hsub : ((layersM n w R ψ').drop i).flatten.Subperm ψ' :=
      (flatten_drop_sublist _ i).subperm.trans (perm_flatten_layersM n w R ψ').subperm
    constructor
    · refine hev _ ⟨?_, ?_, hsub.trans hp'.sublist.subperm⟩
      · rw [hd, hd']; exact hIi.good hli
      · rw [List.length_drop]; omega
    · refine hev _ ⟨?_, ?_, ?_⟩
      · rw [hd']; exact hIi.good_trial C hli
      · rw [List.length_cons, List.length_drop]; omega
      · have h1 : ((C :: (layersM n w R ψ').getD i []) :: (layersM n w R ψ').drop (i + 1)).flatten = C :: ((layersM n w R ψ').drop i).flatten := by
          rw [hd]; simp
        rw [h1]
        exact ((List.subperm_cons C).2 hsub).trans ((List.perm_append_singleton C ψ').symm.subperm.trans hp.sublist.subperm)
end PaddedDescent.F.Mark

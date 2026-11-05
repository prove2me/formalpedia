-- Prove2me | solution 1 for PaddedDescent.F.Mark.Code.enc_append_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:07:46.763221+00:00
-- url     : https://prove2.me/submissions/0d0c0edd-3b2b-478d-a5a9-ad4ed10f1e93

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_PaddedDescent_F_MarkCode
import Theorems.Thm_PaddedDescent_F_Mark_Code_enc_eq
import Theorems.Thm_PaddedDescent_F_Mark_Code_mem_ones
import Theorems.Thm_PaddedDescent_F_Mark_Code_le_blocks_mul
import Theorems.Thm_PaddedDescent_F_Mark_Code_eq_of_blocks
import Theorems.Thm_Groundwork_Decode_enc_eq
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
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
attribute [local fun_prop] Groundwork.PolyT.all
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
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Code
open Groundwork
namespace PaddedDescent.F.Mark.Code
theorem _root_.solution {β b : ℕ} (h0 : 0 < b) (hb : b ≤ 2 ^ β) {x x' r r' : List Bool} (hl : x.length = x'.length)
    (h : enc β b x ++ r = enc β b x' ++ r') : x = x' ∧ r = r' := by
  rw [enc_eq, enc_eq, ← hl] at h
  obtain ⟨h1, h2⟩ := eq_of_blocks hb _ h
  refine ⟨List.ext_getElem hl fun i hi hi' => ?_, h2⟩
  have ho : i / b < (x.length + b - 1) / b := by
    rw [Nat.div_lt_iff_lt_mul h0]
    exact hi.trans_le (le_blocks_mul h0 _)
  have hm := h1 (i / b) (List.mem_range.2 ho)
  have hi2 : i / b * b + i % b = i := by rw [Nat.mul_comm]; exact Nat.div_add_mod i b
  have key : (x.getD i false = true) ↔ (x'.getD i false = true) := by
    have e1 := @mem_ones b x (i / b) (i % b)
    have e2 := @mem_ones b x' (i / b) (i % b)
    rw [hi2] at e1 e2
    rw [hm] at e1
    have hlt := Nat.mod_lt i h0
    exact ⟨fun hx => (e2.1 (e1.2 ⟨hlt, hx⟩)).2, fun hx => (e1.1 (e2.2 ⟨hlt, hx⟩)).2⟩
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi', Option.getD_some] at key
  exact Bool.eq_iff_iff.2 key
end PaddedDescent.F.Mark.Code

-- Prove2me | solution 1 for PaddedDescent.F.Top.correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:57:24.03687+00:00
-- url     : https://prove2.me/submissions/294f7865-98c2-4c56-8dc3-31608ea275a0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_NSat
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_PaddedDescent_F_Top
import Theorems.Thm_PaddedDescent_F_Top_walk_sat
import Theorems.Thm_PaddedDescent_F_Top_inLen_three
import Theorems.Thm_Groundwork_Decode_dec_enc
import Theorems.Thm_Groundwork_Decode_length_enc
import Theorems.Thm_Groundwork_Decode_length_enc_succ_le
import Theorems.Thm_Groundwork_Decode_length_toN
import Theorems.Thm_Groundwork_Decode_mem_toN
import Theorems.Thm_Groundwork_Decode_nil_mem_toN
import Theorems.Thm_Groundwork_Decode_satN_toN
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
open PaddedDescent PaddedDescent.F PaddedDescent.F.Top
open Finset Groundwork Groundwork.Prog
open Groundwork.Sparsify (PFml leaves rootP roundB round)
open WidthK (theta bsum leafC)
open WidthK.Prog (stepK)
open PaddedDescent.F.Mark (WfL occ nSat)
namespace PaddedDescent.F.Top
theorem _root_.solution (hCount : StCountM) (hLf : StLeaf) (hSched : StSched) (hA : StA) (hAW : StAW) : StCorrect (C0K 3) (s0K 3) := by
  intro n φ h3 hs
  obtain ⟨C₀, hC₀, hC8⟩ : ∃ C₀, C₀ = C0K 3 ∧ 8 ≤ C₀ := ⟨_, rfl, Nat.le_mul_of_pos_right 8 (Nat.two_pow_pos _)⟩
  rw [← hC₀]
  obtain ⟨pad, hpad⟩ : ∃ pad : U, pad = List.replicate (2 ^ (C₀ * (n / 2 ^ sOf n + 1))) () := ⟨_, rfl⟩
  rw [← hpad]
  have hF : 2 ^ (8 * (n / 2 ^ sOf n + 1)) ≤ pad.length := by
    rw [hpad, List.length_replicate]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hC8)
  have hdec : Decode.dec (Sat3.enc φ) = (n, Decode.toN φ) := Decode.dec_enc h3.1
  have hnilψ : hasNil (Decode.toN φ) = true ↔ [] ∈ φ := by
    rw [← Decode.nil_mem_toN]
    simp [hasNil, List.any_eq_true]
  simp only [A, decF, hdec]
  by_cases hnil : [] ∈ φ
  · rw [hnilψ.2 hnil]
    simp only [cond_true, Bool.false_eq_true, false_iff]
    rintro ⟨a, ha⟩
    obtain ⟨l, hl, -⟩ := ha [] hnil
    simp at hl
  · have hn' : hasNil (Decode.toN φ) = false := by
      rw [← Bool.not_eq_true]; exact fun h => hnil (hnilψ.1 h)
    have hm : (Decode.toN φ).length ≤ inLen 3 n := by
      have h := Decode.length_enc φ
      have h' := Decode.length_enc_succ_le h3
      have hB : 0 < 3 * (Nat.log2 (2 * n) + 1) := by omega
      have := Nat.le_mul_of_pos_right φ.length hB
      rw [Decode.length_toN, inLen_three]
      omega
    have hψne : ∀ C ∈ Decode.toN φ, C ≠ [] ∧ C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < n := by
      intro D hD
      obtain ⟨⟨C, hC, hl⟩, h⟩ := Decode.mem_toN hD
      refine ⟨?_, hl ▸ h3.1 C hC, h⟩
      rintro rfl
      exact hnil ((Decode.nil_mem_toN φ).1 hD)
    rw [hn', cond_false, walk_sat hCount hLf hSched hA hAW (by norm_num) hs pad hF _ hm hψne]
    exact Decode.satN_toN φ
end PaddedDescent.F.Top

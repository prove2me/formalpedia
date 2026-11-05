-- Prove2me | solution 1 for PaddedDescent.F.Mark.Size.sized_markN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:16:16.090323+00:00
-- url     : https://prove2.me/submissions/2ce1a1d6-a24a-494a-9090-c9425c53beca

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_PaddedDescent_F_MarkSize
import Theorems.Thm_PaddedDescent_F_Mark_Size_mcap_comm
import Theorems.Thm_PaddedDescent_F_Mark_Size_sum_mcap_le
import Theorems.Thm_PaddedDescent_F_Mark_Size_sum_erase_fin
import Theorems.Thm_PaddedDescent_F_Mark_Size_abs_boole_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Count_abs_boole_le
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
import Theorems.Thm_Groundwork_card_words
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
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Size
open Groundwork Groundwork.Prog Finset
variable {g n : ℕ} {Ls : List Fml}
namespace PaddedDescent.F.Mark.Size
theorem _root_.solution {gu nu βu bu : U} {k w y P : ℕ} (h0 : 0 < bu.length) (h : adm k gu.length nu.length w Ls y = true)
    (hP : ∀ a < gu.length, qv gu.length nu.length + (tch gu.length nu.length Ls a).length ≤ P ∧
      2 * (2 + βu.length) * (tch gu.length nu.length Ls a).length ≤ P) :
    (markN gu.length ((gu, nu, βu, bu), (Ls, y))).Sized P 0 where
  card_S a := by
    simp only [markN, markF, card_words]
    exact Nat.pow_le_pow_right (by norm_num) (hP a a.2).1
  c_symm a b := by simp only [markN, markF]; exact mcap_comm _ _ _ _ _
  sum_c a := by
    simp only [markN, markF]
    rw [sum_erase_fin a fun b' => mcap gu.length nu.length βu.length bu.length Ls y a.val b']
    exact (sum_mcap_le h0 h a.2).trans (hP a a.2).2
  card_lab a b _ := by
    simp only [Network.lab, markN, markF, card_words]
    refine Nat.pow_le_pow_right (by norm_num) (le_of_eq ?_)
    rcases le_total a b with hab | hab
    · rw [min_eq_left hab, max_eq_right hab]
    · rw [min_eq_right hab, max_eq_left hab, mcap_comm]
  abs_W a z := by
    simp only [markN, markF, mW, pow_zero]
    split_ifs
    · simp
    · simp
  abs_f a b z θ := by
    simp only [markN, markF, pow_zero]
    exact abs_boole_le _
  abs_Ψ a b z z' _ := by
    simp only [Network.Ψ, markN, markF, pow_zero]
    have e : ∀ (L L' θ : List Bool), ((if (L == θ) = true then (1 : ℤ) else 0) * if (L' == θ) = true then 1 else 0) =
        if θ = L ∧ θ = L' then 1 else 0 := by
      intro L L' θ
      by_cases h1 : θ = L
      · by_cases h2 : θ = L'
        · subst h1; simp [← h2]
        · have h2' : ¬ L' = θ := fun h => h2 h.symm
          simp [h2, h2']
      · have h1' : ¬ L = θ := fun h => h1 h.symm
        simp [h1, h1']
    simp only [e]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, abs_of_nonneg (Nat.cast_nonneg _)]
    refine Nat.cast_le_one.2 (card_le_one.2 fun θ hθ θ' hθ' => ?_)
    exact ((mem_filter.1 hθ).2.1).trans ((mem_filter.1 hθ').2.1).symm
end PaddedDescent.F.Mark.Size

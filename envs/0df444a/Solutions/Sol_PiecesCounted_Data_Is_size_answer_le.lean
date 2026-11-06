-- Prove2me | solution 1 for PiecesCounted.Data.Is.size_answer_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:10:38.946635+00:00
-- url     : https://prove2.me/submissions/a7b3f5d1-32cc-41b6-91cf-999b19e46b0a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCounted_Basic
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Sizes
import Theorems.Thm_PiecesCounted_size_int_le
import Theorems.Thm_PiecesCounted_size_natCast_le
import Theorems.Thm_PiecesCounted_size_ints_le
import Theorems.Thm_PiecesCounted_Data_Is_cap_le
import Theorems.Thm_GeneralPieces_Trim_length_bitsOf
import Theorems.Thm_GeneralPieces_Trim_length_rep
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_NetE_cap_le
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
import Theorems.Thm_PiecesCounted_oracle_eq_some
import Theorems.Thm_QueryMachines_QueryMachine_close_bind
import Theorems.Thm_QueryMachines_QueryMachine_close_both
import Theorems.Thm_QueryMachines_QueryMachine_close_branch
import Theorems.Thm_QueryMachines_QueryMachine_close_const
import Theorems.Thm_QueryMachines_QueryMachine_close_foldRange
import Theorems.Thm_QueryMachines_QueryMachine_close_foldWhile
import Theorems.Thm_QueryMachines_QueryMachine_close_gated
import Theorems.Thm_QueryMachines_QueryMachine_close_ite
import Theorems.Thm_QueryMachines_QueryMachine_close_lift
import Theorems.Thm_QueryMachines_QueryMachine_close_mapAsk
import Theorems.Thm_QueryMachines_QueryMachine_close_mapIn
import Theorems.Thm_QueryMachines_QueryMachine_close_mapOut
import Theorems.Thm_QueryMachines_QueryMachine_close_optBind
import Theorems.Thm_QueryMachines_QueryMachine_close_prodRange
import Theorems.Thm_QueryMachines_QueryMachine_close_query
import Theorems.Thm_QueryMachines_QueryMachine_close_subst
import Theorems.Thm_QueryMachines_QueryMachine_close_sumRange
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] GeneralPieces.Trim.length_bitsOf
attribute [local simp] GeneralPieces.Trim.length_rep
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
attribute [local simp] QueryMachines.QueryMachine.close_bind
attribute [local simp] QueryMachines.QueryMachine.close_both
attribute [local simp] QueryMachines.QueryMachine.close_branch
attribute [local simp] QueryMachines.QueryMachine.close_const
attribute [local simp] QueryMachines.QueryMachine.close_foldRange
attribute [local simp] QueryMachines.QueryMachine.close_foldWhile
attribute [local simp] QueryMachines.QueryMachine.close_gated
attribute [local simp] QueryMachines.QueryMachine.close_ite
attribute [local simp] QueryMachines.QueryMachine.close_lift
attribute [local simp] QueryMachines.QueryMachine.close_mapAsk
attribute [local simp] QueryMachines.QueryMachine.close_mapIn
attribute [local simp] QueryMachines.QueryMachine.close_mapOut
attribute [local simp] QueryMachines.QueryMachine.close_optBind
attribute [local simp] QueryMachines.QueryMachine.close_prodRange
attribute [local simp] QueryMachines.QueryMachine.close_query
attribute [local simp] QueryMachines.QueryMachine.close_subst
attribute [local simp] QueryMachines.QueryMachine.close_sumRange



set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog
namespace PiecesCounted
namespace Data.Is
theorem _root_.solution {D : Data} {ρ : ℝ} {c : ℕ} (h : D.Is ρ c) {g : List Unit × Question} {a : Answer} (hg : D.oracle g = some a) :
    size a ≤ (2 * g.1.length) ^ c * ((2 * g.1.length) ^ c + 2) + (c * g.1.length + 4 * g.1.length) + 2 := by
  obtain ⟨hl, ha⟩ := oracle_eq_some hg
  obtain ⟨u, q⟩ := g
  dsimp only at hl ha ⊢
  have hX : (2 * u.length) ^ c ≤ (2 * u.length) ^ c * ((2 * u.length) ^ c + 2) := Nat.le_mul_of_pos_right _ (by omega)
  rcases q with q | q | q | q | q
  · obtain rfl : Sum.inl (D.fam u.length).d = a := Option.some.inj ha
    have h0 : (0 : ℤ) ≤ (D.fam u.length).d := by have := h.d_pos _ hl; omega
    have h1 : |(D.fam u.length).d| < 2 ^ (2 * u.length) ^ c := by rw [abs_of_nonneg h0]; exact h.size_d _ hl
    have := size_int_le h1
    rw [size_inl]
    omega
  · obtain rfl := Option.some.inj ha
    have h1 : size (D.fam u.length).I.sort ≤ (D.fam u.length).I.sort.length * ((2 * u.length) ^ c + 2) + 1 :=
      size_ints_le (s := (2 * u.length) ^ c + 1) fun x hx => size_int_le (h.size_I _ hl x ((Finset.mem_sort _).1 hx))
    rw [Finset.length_sort] at h1
    have h2 := Nat.mul_le_mul_right ((2 * u.length) ^ c + 2) (h.card _ hl)
    rw [size_inr]
    omega
  · simp only [Data.answer] at ha
    split at ha
    · rename_i hi
      obtain rfl := Option.some.inj ha
      have := size_natCast_le (D.cap u.length q.1 q.2)
      have := h.cap_le hl hi q.1
      rw [size_inl]
      omega
    · cases ha
  · simp only [Data.answer] at ha
    split at ha
    · rename_i hi
      obtain rfl := Option.some.inj ha
      have := size_int_le (h.size_A _ hl _ hi.1 (toBits _ q.2.1) (toBits _ q.2.2.1) (toBits _ q.2.2.2.1) (toBits _ q.2.2.2.2))
      rw [size_inl]
      omega
    · cases ha
  · simp only [Data.answer] at ha
    split at ha
    · rename_i hi
      obtain rfl := Option.some.inj ha
      have := size_int_le (h.size_f _ hl _ hi.1 q.1.1 q.1.2 (toBits _ q.2.2.1, toBits _ q.2.2.2.1) q.2.2.2.2 (mem_words.2 hi.2.2.2))
      rw [size_inl]
      omega
    · cases ha
end Data.Is
end PiecesCounted

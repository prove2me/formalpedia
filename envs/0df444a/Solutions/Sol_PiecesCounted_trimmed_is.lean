-- Prove2me | solution 1 for PiecesCounted.trimmed_is
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:12:13.362951+00:00
-- url     : https://prove2.me/submissions/266cfeee-8c6a-4028-be04-4ca7d7a859cc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_PiecesCounted_Sizes
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_GeneralPieces_Trim_Prog
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Trimmed
import Theorems.Thm_PiecesCounted_trimmed_cap
import Theorems.Thm_PiecesCounted_trimmed_fn_of_le
import Theorems.Thm_PiecesCounted_trimmed_fn_first
import Theorems.Thm_PiecesCounted_trimmed_fn_row
import Theorems.Thm_PiecesCounted_trimmed_fn_col
import Theorems.Thm_PiecesCounted_toBits_take
import Theorems.Thm_PiecesCounted_toBits_drop
import Theorems.Thm_PiecesCounted_sum_indicator
import Theorems.Thm_GeneralPieces_Trim_length_bitsOf
import Theorems.Thm_GeneralPieces_Trim_length_rep
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_sum
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
attribute [local fun_prop] Groundwork.PolyT.sum
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
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution {D : Data} {ρ : ℝ} {c : ℕ} (h : D.Is ρ c) : (trimmed D).Is ρ c := by
  have hX : ∀ lam, 1 ≤ lam → (1 : ℤ) < 2 ^ (2 * lam) ^ c := fun lam hl => one_lt_pow₀ (by norm_num) (Nat.pos_iff_ne_zero.1 (Nat.pow_pos (by omega)))
  refine ⟨h.rho_ge, h.rho_lt, h.c_pos, h.d_pos, h.sum, fun lam hl i hi x y u v => ?_, fun lam hl i hi x y u v => ?_, fun lam hl i hi => ?_, h.card, h.size_d, h.size_I, h.size_A,
    fun lam hl i hi tr side z θ hθ => ?_⟩
  · change (D.fam lam).A i x y u v = _
    rw [trimmed_cap]
    by_cases hc : D.cap lam false i ≤ 2 * lam
    · rw [min_eq_left hc]
      simp only [trimmed_fn_of_le hc]
      exact h.row lam hl i hi x y u v
    · rw [min_eq_right (by omega)]
      simp only [trimmed_fn_first hc, trimmed_fn_row hc]
      rw [sum_indicator x y fun θ => (D.fam lam).A i (toBits lam (θ.take lam)) (toBits lam (θ.drop lam)) u v, toBits_take, toBits_drop]
  · change (D.fam lam).A i x y u v = _
    rw [trimmed_cap]
    by_cases hc : D.cap lam true i ≤ 2 * lam
    · rw [min_eq_left hc]
      simp only [trimmed_fn_of_le hc]
      exact h.col lam hl i hi x y u v
    · rw [min_eq_right (by omega)]
      simp only [trimmed_fn_first hc, trimmed_fn_col hc]
      rw [sum_indicator x u fun θ => (D.fam lam).A i (toBits lam (θ.take lam)) y (toBits lam (θ.drop lam)) v, toBits_take, toBits_drop]
  · refine le_trans ?_ (h.caps lam hl i hi)
    rw [trimmed_cap, trimmed_cap]
    exact_mod_cast Nat.add_le_add (min_le_left _ _) (min_le_left _ _)
  · by_cases hc : D.cap lam tr i ≤ 2 * lam
    · rw [trimmed_fn_of_le hc]
      rw [trimmed_cap, min_eq_left hc] at hθ
      exact h.size_f lam hl i hi tr side z θ hθ
    · cases side
      · rw [trimmed_fn_first hc]
        have := hX lam hl
        split
        · simpa using this
        · simp
      · cases tr
        · rw [trimmed_fn_row hc]
          exact h.size_A lam hl i hi _ _ _ _
        · rw [trimmed_fn_col hc]
          exact h.size_A lam hl i hi _ _ _ _
end PiecesCounted

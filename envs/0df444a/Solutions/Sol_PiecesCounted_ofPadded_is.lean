-- Prove2me | solution 1 for PiecesCounted.ofPadded_is
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:50:26.082313+00:00
-- url     : https://prove2.me/submissions/50167be2-059d-44e5-8ac7-d9f4dccdc3c2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_PaddedData
import Theorems.Thm_PiecesCounted_toNat_shift
import Theorems.Thm_PiecesCounted_mem_ofPadded
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_sum
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
attribute [local fun_prop] Groundwork.PolyT.sum
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
theorem _root_.solution {ρ : ℝ} {c : ℕ} {P : PiecesF} {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : AppRunningTime.ValQ → ℤ} {shift : ℕ → ℤ} (h : AppRunningTime.IsPieces ρ c P A val)
    (hs : ∀ lam, 1 ≤ lam → |shift lam| + (2 * lam) ^ c < 2 ^ (2 * lam) ^ c) : (ofPadded P A c shift).Is ρ c := by
  have hp : ∀ lam, 2 ^ (c * lam) ≤ (List.replicate (2 ^ (c * lam)) ()).length := fun lam => by rw [List.length_replicate]
  refine ⟨h.rho_ge, h.rho_lt, h.c_pos, fun lam hl => ?_, fun lam hl x y u v => ?_, fun lam hl i hi x y u v => ?_, fun lam hl i hi x y u v => ?_, fun lam hl i hi => ?_, fun lam hl => ?_,
    fun lam hl => ?_, fun lam hl i hi => ?_, fun lam hl i hi x y u v => ?_, fun lam hl i hi tr side z θ _ => ?_⟩
  · change (1 : ℤ) ≤ (P.d 0 lam : ℤ)
    exact_mod_cast h.d_pos lam hl
  · refine Eq.trans ?_ (h.sum lam hl x y u v)
    exact (Finset.sum_image fun a _ b _ e => by simpa using e).trans (Finset.sum_congr rfl fun j _ => by
      change A lam ((j : ℤ) + shift lam - shift lam).toNat x y u v = _
      rw [toNat_shift])
  · obtain ⟨j, hj, rfl⟩ := mem_ofPadded hi
    change A lam ((j : ℤ) + shift lam - shift lam).toNat x y u v = ∑ θ ∈ words (P.cap false 0 lam ((j : ℤ) + shift lam - shift lam).toNat),
      P.top ((List.replicate (2 ^ (c * lam)) (), false), (0, ((j : ℤ) + shift lam - shift lam).toNat), (bitsOf x, bitsOf y, θ)) *
        P.bot ((List.replicate (2 ^ (c * lam)) (), false), (0, ((j : ℤ) + shift lam - shift lam).toNat), (bitsOf u, bitsOf v, θ))
    rw [toNat_shift]
    exact h.row lam hl _ (hp lam) j hj x y u v
  · obtain ⟨j, hj, rfl⟩ := mem_ofPadded hi
    change A lam ((j : ℤ) + shift lam - shift lam).toNat x y u v = ∑ θ ∈ words (P.cap true 0 lam ((j : ℤ) + shift lam - shift lam).toNat),
      P.top ((List.replicate (2 ^ (c * lam)) (), true), (0, ((j : ℤ) + shift lam - shift lam).toNat), (bitsOf x, bitsOf u, θ)) *
        P.bot ((List.replicate (2 ^ (c * lam)) (), true), (0, ((j : ℤ) + shift lam - shift lam).toNat), (bitsOf y, bitsOf v, θ))
    rw [toNat_shift]
    exact h.col lam hl _ (hp lam) j hj x y u v
  · obtain ⟨j, hj, rfl⟩ := mem_ofPadded hi
    change ((P.cap false 0 lam ((j : ℤ) + shift lam - shift lam).toNat + P.cap true 0 lam ((j : ℤ) + shift lam - shift lam).toNat : ℕ) : ℝ) ≤ _
    rw [toNat_shift]
    exact h.caps lam hl j hj
  · exact Finset.card_image_le.trans (by rw [Finset.card_range]; exact h.card lam hl)
  · change (P.d 0 lam : ℤ) < 2 ^ (2 * lam) ^ c
    exact_mod_cast h.size_d lam hl
  · obtain ⟨j, hj, rfl⟩ := mem_ofPadded hi
    have h1 : (j : ℤ) < (2 * (lam : ℤ)) ^ c := by exact_mod_cast hj.trans_le (h.card lam hl)
    have h2 := hs lam hl
    have h3 := le_abs_self (shift lam)
    have h4 := neg_abs_le (shift lam)
    have h5 : (0 : ℤ) ≤ j := Int.natCast_nonneg j
    rw [abs_lt]
    constructor <;> linarith
  · obtain ⟨j, hj, rfl⟩ := mem_ofPadded hi
    change |A lam ((j : ℤ) + shift lam - shift lam).toNat x y u v| < _
    rw [toNat_shift]
    exact h.size_A lam hl j hj x y u v
  · obtain ⟨j, hj, rfl⟩ := mem_ofPadded hi
    have h1 := h.size_f lam hl _ (hp lam) j hj tr z.1 z.2 θ
    cases side
    · change |P.top ((List.replicate (2 ^ (c * lam)) (), tr), (0, ((j : ℤ) + shift lam - shift lam).toNat), (bitsOf z.1, bitsOf z.2, θ))| < _
      rw [toNat_shift]
      exact h1.1
    · change |P.bot ((List.replicate (2 ^ (c * lam)) (), tr), (0, ((j : ℤ) + shift lam - shift lam).toNat), (bitsOf z.1, bitsOf z.2, θ))| < _
      rw [toNat_shift]
      exact h1.2
end PiecesCounted

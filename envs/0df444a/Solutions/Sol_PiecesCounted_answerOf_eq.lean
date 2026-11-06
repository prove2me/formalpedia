-- Prove2me | solution 1 for PiecesCounted.answerOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:10:15.654139+00:00
-- url     : https://prove2.me/submissions/9dca0e1f-d447-4b67-a262-184fcfbf5009

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCounted_PadThen
import Definitions.Def_PiecesCounted_PaddedData
import Definitions.Def_PiecesCounted_Sizes
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Padded
import Theorems.Thm_GeneralPieces_Trim_length_bitsOf
import Theorems.Thm_GeneralPieces_Trim_length_rep
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
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
import Theorems.Thm_PiecesCounted_bitsOf_toBits
import Theorems.Thm_PiecesCounted_mem_ofPadded
import Theorems.Thm_PiecesCounted_oracle_eq_some
import Theorems.Thm_PiecesCounted_sort_image_shift
import Theorems.Thm_PiecesCounted_toNat_shift
import Theorems.Thm_PiecesCounted_units_eq
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
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution {ρ : ℝ} {c : ℕ} {P : PiecesF} {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : AppRunningTime.ValQ → ℤ} {shift : ℕ → ℤ} (h : AppRunningTime.IsPieces ρ c P A val)
    {g : List Unit × Question} {a : Answer} (hg : (ofPadded P A c shift).oracle g = some a) : answerOf P val shift (g, List.replicate (2 ^ (c * g.1.length)) ()) = a := by
  obtain ⟨hl, ha⟩ := oracle_eq_some hg
  obtain ⟨u, q⟩ := g
  dsimp only at hl ha ⊢
  rcases q with q | q | q | q | q
  · obtain rfl := Option.some.inj ha
    rfl
  · obtain rfl := Option.some.inj ha
    exact congrArg Sum.inr (sort_image_shift _ _).symm
  · simp only [Data.answer] at ha
    split at ha
    · obtain rfl := Option.some.inj ha
      obtain ⟨tr, i⟩ := q
      cases tr <;> rfl
    · cases ha
  · simp only [Data.answer] at ha
    split at ha
    · rename_i hi
      obtain rfl := Option.some.inj ha
      obtain ⟨i, l1, l2, l3, l4⟩ := q
      obtain ⟨hi, e1, e2, e3, e4⟩ := hi
      dsimp only at hi e1 e2 e3 e4
      obtain ⟨j, hj, rfl⟩ := mem_ofPadded hi
      have h1 := h.val_eq u.length hl (List.replicate (2 ^ (c * u.length)) ()) (by rw [List.length_replicate]) j hj (toBits _ l1) (toBits _ l2) (toBits _ l3) (toBits _ l4)
      rw [bitsOf_toBits e1, bitsOf_toBits e2, bitsOf_toBits e3, bitsOf_toBits e4, units_eq] at h1
      change Sum.inl (val (List.replicate (2 ^ (c * u.length)) (), (u, ((j : ℤ) + shift u.length - shift u.length).toNat), (l1, l2, l3, l4))) =
        Sum.inl (A u.length ((j : ℤ) + shift u.length - shift u.length).toNat (toBits _ l1) (toBits _ l2) (toBits _ l3) (toBits _ l4))
      rw [toNat_shift, h1]
    · cases ha
  · simp only [Data.answer] at ha
    split at ha
    · rename_i hi
      obtain rfl := Option.some.inj ha
      obtain ⟨⟨tr, side⟩, i, l1, l2, θ⟩ := q
      obtain ⟨hi, e1, e2, e3⟩ := hi
      dsimp only at hi e1 e2 e3
      cases side
      · change Sum.inl (P.top ((List.replicate (2 ^ (c * u.length)) (), tr), (0, (i - shift u.length).toNat), (l1, l2, θ))) =
          Sum.inl (P.top ((List.replicate (2 ^ (c * u.length)) (), tr), (0, (i - shift u.length).toNat), (bitsOf (toBits u.length l1), bitsOf (toBits u.length l2), θ)))
        rw [bitsOf_toBits e1, bitsOf_toBits e2]
      · change Sum.inl (P.bot ((List.replicate (2 ^ (c * u.length)) (), tr), (0, (i - shift u.length).toNat), (l1, l2, θ))) =
          Sum.inl (P.bot ((List.replicate (2 ^ (c * u.length)) (), tr), (0, (i - shift u.length).toNat), (bitsOf (toBits u.length l1), bitsOf (toBits u.length l2), θ)))
        rw [bitsOf_toBits e1, bitsOf_toBits e2]
    · cases ha
end PiecesCounted

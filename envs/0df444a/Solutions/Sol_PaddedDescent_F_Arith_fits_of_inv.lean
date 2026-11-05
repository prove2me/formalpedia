-- Prove2me | solution 1 for PaddedDescent.F.Arith.fits_of_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:21:42.903212+00:00
-- url     : https://prove2.me/submissions/2649cf39-dec3-474e-8ae5-7b7c2fdaa7b5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithInv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_PaddedDescent_F_ArithFits
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
import Theorems.Thm_PaddedDescent_F_Arith_Inv_bottom_le
import Theorems.Thm_PaddedDescent_F_Arith_Inv_lab_le
import Theorems.Thm_PaddedDescent_F_Arith_Inv_mul_le
import Theorems.Thm_PaddedDescent_F_Arith_Inv_pat_le
import Theorems.Thm_PaddedDescent_F_Arith_Inv_st_le
import Theorems.Thm_PaddedDescent_F_Arith_Inv_step
import Theorems.Thm_PaddedDescent_F_Arith_Inv_work_le
import Theorems.Thm_PaddedDescent_F_Arith_col_le
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
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open Groundwork.Prog (nRect)
namespace PaddedDescent.F.Arith
theorem _root_.solution {t X Z Qm Wm L Lw e F : ℕ} (hZ : 25 * Kseq t ^ 2 ≤ 2 * Z) (hZQ : Z ≤ Qm) (hL : Qm + 1 ≤ 2 ^ L)
    (hLw : Kseq t * (3 * Wm + 14) + 4 * Qm + 10 ≤ 2 ^ Lw)
    (he1 : 4 * (X + Z) ≤ e) (he2 : L * Kseq t ^ 2 ≤ e) (he3 : Kseq t ≤ e)
    (he4 : L * (2 * Kseq t ^ 2) + (X + Z) + Lw + 1 ≤ e) (hF : 2 ^ e ≤ F) :
    ∀ j, j ≤ t → ∀ lam B cnt, Inv t X Z Qm Wm L j lam B cnt → Fits F (Kseq j) lam B cnt (schedL j) := by
  have up : ∀ {a : ℕ}, a ≤ e → 2 ^ a ≤ F := fun h => (Nat.pow_le_pow_right (by norm_num) h).trans hF
  intro j
  induction j with
  | zero =>
    intro hj lam B cnt h
    exact ⟨(h.work_le hLw hj).trans (up he4), up (h.bottom_le.trans (by omega))⟩
  | succ j ih =>
    intro hj lam B cnt h
    have h' := h.step hZ hZQ hL hj
    simp only [schedL, Fits, List.length_replicate]
    refine ⟨(h.work_le hLw hj).trans (up he4), ⟨?_, ?_, ?_, ?_, ?_⟩, ih (by omega) _ _ _ h'⟩
    · exact (h.pat_le hL hj).trans (up he2)
    · exact (col_le hj).trans (up he3)
    · exact up (h.st_le.trans he1)
    · exact up (h.lab_le.trans (by omega))
    · exact up (le_trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) (h'.mul_le.trans (by omega)))
end PaddedDescent.F.Arith

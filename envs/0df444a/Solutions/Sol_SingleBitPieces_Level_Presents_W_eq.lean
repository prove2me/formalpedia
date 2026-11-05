-- Prove2me | solution 1 for SingleBitPieces.Level.Presents.W_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:20:01.903328+00:00
-- url     : https://prove2.me/submissions/7d04f23e-ad7c-423f-ac21-effe3f35352a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecCrossing_Crossing
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_SingleBitPieces_SecCrossing_PolyA
import Definitions.Def_ToTuring_Lib_Table
import Definitions.Def_SingleBitPieces_SecNetworks_LemGrouping
import Definitions.Def_Paper_SecLevel_Recursion
import Definitions.Def_ClauseBound_Alg_Grid
import Mathlib.Tactic
import Definitions.Def_SingleBitPieces_Level_Presents
import Theorems.Thm_SingleBitPieces_Level_Presents_nMemb_self
import Theorems.Thm_SingleBitPieces_Level_Presents_sideChk_eq
import Theorems.Thm_ClauseBound_Alg_GridNet_gridE_symm_val
import Theorems.Thm_ClauseBound_Alg_GridNet_nodeG_lt
import Theorems.Thm_ClauseBound_Alg_GridPresents_chkG_iff
import Theorems.Thm_ClauseBound_Alg_GridPresents_gridN_W
import Theorems.Thm_Groundwork_Grid_gridE_symm_val
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_congr
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
attribute [local fun_prop] Groundwork.PolyT.length
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
open SingleBitPieces SingleBitPieces.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Stepped
open SingleBitPieces.Level.Presents
namespace SingleBitPieces.Level.Presents
theorem _root_.solution (P : PiecesF) {C : Type} {g : ℕ} (tr : Bool) (lam : C → ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (c : C) (y : ℕ) (a : Fin (nParts g g tr))
    {z : List Bool} (hz : z.length = nMemb g g tr * (g * g) * lam c) :
    (gridN P [] g g tr 0 (lam c) y Rm).W a z = sideWv g tr (lam c) Rm (sideChk g tr lam ((c, y), (a.val, z))) a z := by
  rw [gridN_W P [] g g tr 0 (lam c) y Rm a hz, sideChk_eq, sideWv]
  by_cases hc : chkG g g tr (lam c) (a.val, z) = true
  · obtain ⟨h1, h2⟩ := (chkG_iff g g tr (lam c) a z).1 hc
    have e0 : ∀ F : ℕ → ℤ, ∏ i ∈ range g, F i = ∏ i ∈ range (nMemb g g tr), F i := fun F => by rw [nMemb_self]
    rw [if_pos hc, Finset.prod_eq_one (s := pairs (Fin (nMemb g g tr))) fun q hq => if_pos (h2 q hq), mul_one, e0, Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hn : node g tr a i < g * g := nodeG_lt tr a.2 i.2
    rw [if_pos (h1 i), dif_pos hn]
    have e : (GridNet.gridE g g tr).symm (a, i) = ⟨node g tr a i, hn⟩ := Fin.ext (GridNet.gridE_symm_val g g tr (a, i))
    rw [e]
    congr 1
    funext u
    simp only [sideLabels, Fin.ext_iff]
    rfl
  · rw [if_neg hc]
    rw [chkG_iff, not_and_or] at hc
    rcases hc with h | h
    · push Not at h
      obtain ⟨i, hi⟩ := h
      rw [Finset.prod_eq_zero (mem_univ i) (if_neg hi), zero_mul]
    · push Not at h
      obtain ⟨q, hq, hne⟩ := h
      rw [Finset.prod_eq_zero hq (if_neg hne), mul_zero]
end SingleBitPieces.Level.Presents

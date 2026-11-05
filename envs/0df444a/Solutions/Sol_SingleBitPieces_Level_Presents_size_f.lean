-- Prove2me | solution 1 for SingleBitPieces.Level.Presents.size_f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:17:56.150511+00:00
-- url     : https://prove2.me/submissions/fab78062-7344-40fc-a4ae-99186ee9a44d

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
import Theorems.Thm_SingleBitPieces_Level_Presents_size_int_le
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_sideA_mul
import Theorems.Thm_Groundwork_Prog_side_size_of
import Theorems.Thm_Groundwork_Prog_size_bools
import Theorems.Thm_Groundwork_Prog_size_nat_le
import Theorems.Thm_Groundwork_Prog_size_pattern_le
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
theorem _root_.solution {C : Type} [HasSize C] (g B S lm : ℕ) (hl : 1 ≤ lm) (c : C) {y a b : ℕ} {z θ : List Bool} {v : ℤ}
    (hy : y < (lm + 1) ^ nRect g) (ha : a < g) (hb : b < g) (hz : z.length = g ^ 3 * lm) (hθ : θ.length ≤ g ^ 2 * lm)
    (hv : |v| ≤ 2 ^ (g * B + g ^ 2 * (2 * lm))) :
    max (size ((c, y), ((a, b), (z, θ)))) (size v) + 1 ≤ S + sideA g * (size c + B + lm) ^ sideA g := by
  refine side_size_of ?_
  have h3 := sideA_mul g (size c + B + lm)
  have hY := size_pattern_le hy
  have hV := size_int_le hv
  have e4 : g ^ 4 * (size c + B + lm) = g ^ 4 * size c + g ^ 4 * B + g ^ 4 * lm := by ring
  have e3 : g ^ 3 * (size c + B + lm) = g ^ 3 * size c + g ^ 3 * B + g ^ 3 * lm := by ring
  have e2 : g ^ 2 * (size c + B + lm) = g ^ 2 * size c + g ^ 2 * B + g ^ 2 * lm := by ring
  have e1 : g * (size c + B + lm) = g * size c + g * B + g * lm := by ring
  have e0 : g ^ 2 * (2 * lm) = 2 * (g ^ 2 * lm) := by ring
  have hg : g ≤ g * lm := Nat.le_mul_of_pos_right _ hl
  have s1 := size_nat_le a
  have s2 := size_nat_le b
  clear hv hy
  have hq : size ((c, y), ((a, b), (z, θ))) + 1 ≤ S + sideA g * (size c + B + lm) := by
    simp only [size_prod, size_bools, hz]
    omega
  have hw : size v + 1 ≤ S + sideA g * (size c + B + lm) := by omega
  exact Nat.succ_le_of_lt (max_lt (Nat.lt_of_succ_le hq) (Nat.lt_of_succ_le hw))
end SingleBitPieces.Level.Presents

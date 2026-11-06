-- Prove2me | solution 1 for VariableBound.ArithNat.argD_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:40:49.743949+00:00
-- url     : https://prove2.me/submissions/788d8f2e-6364-4181-b44a-6c4562c56478

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_ArithDefs
import Definitions.Def_UniformInK_Top_ArithNat
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Budget
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Top_ArithNat
import Theorems.Thm_VariableBound_ArithNat_UbD_le
import Theorems.Thm_VariableBound_ArithNat_gPD_le
import Theorems.Thm_VariableBound_ArithNat_g_le_n
import Theorems.Thm_VariableBound_ArithNat_bitsS_eq
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_pow_le_n
import Theorems.Thm_ClauseBound_TopN_Arith_lamS_mul_le
import Theorems.Thm_ClauseBound_TopN_Arith_pow_le_n
import Theorems.Thm_ClauseBound_TopN_Arith_size_n_le
import Theorems.Thm_ClauseBound_TopN_Arith_succ_le_two_pow
import Theorems.Thm_ClauseBound_TopN_add_le_pow
import Theorems.Thm_ClauseBound_TopN_mul_le_pow
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
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
attribute [local fun_prop] Groundwork.PolyT.all
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
open VariableBound VariableBound.ArithNat
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks UniformInK UniformInK.ArithNat VariableBound.Net
variable {β k K n C₀ : ℕ}
namespace VariableBound.ArithNat
theorem _root_.solution (hB : StBounds) (hkβ : k ≤ β) (hbD : β + 3 ≤ 2 ^ β) (hK : 2 ≤ K) (hn17 : K ^ 17 ≤ n) (hlt : n < K ^ (17 * C₀)) (hD : 2 ^ β ≤ n + 1) :
    K * (lamS K (3 * K ^ 8) (UbD k K n (2 ^ β)) (PbD K n (2 ^ β)) + bitsS K (3 * K ^ 8) (PbD K n (2 ^ β)) (BbD k n))
      ≤ 2 ^ (5 * (17 * C₀ * K.size) + 16) := by
  have hβ : 1 ≤ β := by
    rcases Nat.eq_zero_or_pos β with h | h
    · subst h; omega
    · exact h
  have hK1 : 1 ≤ K := by omega
  have hn1 := succ_le_two_pow hlt
  have hz := size_n_le hlt
  obtain ⟨t, ht⟩ : ∃ t, t = 17 * C₀ * K.size := ⟨_, rfl⟩
  rw [← ht] at hn1 hz ⊢
  have hnt : n ≤ 2 ^ t := by omega
  have hKn : K ≤ n := by simpa using pow_le_n hK1 hn17 (j := 1) (by norm_num)
  have hn0 : 1 ≤ n := hK1.trans hKn
  have hKt : K ≤ 2 ^ t := hKn.trans hnt
  have hDt : 2 ^ β ≤ 2 ^ t := hD.trans hn1
  have hbt : β + 3 ≤ 2 ^ t := hbD.trans hDt
  have hb1t : β + 1 ≤ 2 ^ t := by omega
  have hkt : k ≤ 2 ^ t := by omega
  have hk1t : k + 1 ≤ 2 ^ t := by omega
  have hK16 : K ^ 16 ≤ 2 ^ t := (pow_le_n hK1 hn17 (by norm_num)).trans hnt
  have hK15 : K ^ 15 ≤ 2 ^ t := (pow_le_n hK1 hn17 (by norm_num)).trans hnt
  have hK3 : K ^ 3 ≤ 2 ^ t := (pow_le_n hK1 hn17 (by norm_num)).trans hnt
  have hzt : n.size ≤ 2 ^ t := hz.trans Nat.lt_two_pow_self.le
  have u1 : 140 * k * n * (β + 1) ≤ 2 ^ (8 + t + t + t) := mul_le_pow (mul_le_pow (mul_le_pow (by norm_num) hkt) hnt) hb1t
  have u2 : 18 * K ^ 16 ≤ 2 ^ (5 + t) := mul_le_pow (by norm_num) hK16
  have hUb : UbD k K n (2 ^ β) ≤ 2 ^ (3 * t + 9) := (UbD_le hB hβ hn0).trans (add_le_pow u1 u2 (by omega) (by omega))
  have v1 : 842 * (β + 3) ≤ 2 ^ (10 + t) := mul_le_pow (by norm_num) hbt
  have v2 : 4 * n.size ≤ 2 ^ (2 + t) := mul_le_pow (by norm_num) hzt
  have hgP : 3 * K ^ 8 * PbD K n (2 ^ β) ≤ 2 ^ (t + t + (t + 11)) :=
    (gPD_le hB hβ hn0 (g_le_n hK hn17)).trans (mul_le_pow (mul_le_pow hnt hDt) (add_le_pow v1 v2 (by omega) (by omega)))
  have hlam : lamS K (3 * K ^ 8) (UbD k K n (2 ^ β)) (PbD K n (2 ^ β)) ≤ 2 ^ (4 * t + 12) := by
    have h1 := lamS_mul_le K (3 * K ^ 8) (UbD k K n (2 ^ β)) (PbD K n (2 ^ β))
    have h2 : lamS K (3 * K ^ 8) (UbD k K n (2 ^ β)) (PbD K n (2 ^ β)) ≤
        lamS K (3 * K ^ 8) (UbD k K n (2 ^ β)) (PbD K n (2 ^ β)) * K ^ 3 := Nat.le_mul_of_pos_right _ (by positivity)
    have h3 : K ^ 3 + K * UbD k K n (2 ^ β) ≤ 2 ^ (4 * t + 10) := add_le_pow hK3 (mul_le_pow hKt hUb) (by omega) (by omega)
    exact (h2.trans h1).trans (add_le_pow h3 hgP (by omega) (by omega))
  have hBt : bitsS K (3 * K ^ 8) (PbD K n (2 ^ β)) (BbD k n) ≤ 2 ^ (3 * t + 13) := by
    rw [bitsS_eq hK1]
    have h7 : K ^ 7 ≤ K ^ 8 := Nat.pow_le_pow_right hK1 (by norm_num)
    have h8 : K ^ 8 ≤ K ^ 15 := Nat.pow_le_pow_right hK1 (by norm_num)
    have p1 : PbD K n (2 ^ β) * (6 * K ^ 7) ≤ 2 ^ (t + t + (t + 11) + 1) := by
      rw [pow_succ]
      calc PbD K n (2 ^ β) * (6 * K ^ 7) ≤ PbD K n (2 ^ β) * (6 * K ^ 8) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h7)
        _ = 3 * K ^ 8 * PbD K n (2 ^ β) * 2 := by ring
        _ ≤ 2 ^ (t + t + (t + 11)) * 2 := Nat.mul_le_mul_right _ hgP
    have p2 : BbD k n ≤ 2 ^ (2 * t + 5) := by
      unfold BbD BD
      exact add_le_pow (q := 0) (mul_le_pow hk1t (mul_le_pow (p := 4) (by norm_num) hnt)) (by norm_num) (by omega) (by omega)
    have p3 : 6 * K ^ 8 + 36 * K ^ 15 ≤ 2 ^ (6 + t) :=
      (by omega : 6 * K ^ 8 + 36 * K ^ 15 ≤ 42 * K ^ 15).trans (mul_le_pow (by norm_num) hK15)
    exact add_le_pow p1 (mul_le_pow p2 p3) (by omega) (by omega)
  have hsum := add_le_pow (r := 4 * t + 14) hlam hBt (by omega) (by omega)
  exact (mul_le_pow hKt hsum).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
end VariableBound.ArithNat

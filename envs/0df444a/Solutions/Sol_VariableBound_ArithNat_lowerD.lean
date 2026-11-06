-- Prove2me | solution 1 for VariableBound.ArithNat.lowerD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:47:42.081864+00:00
-- url     : https://prove2.me/submissions/94f4db9c-f1b0-4067-b7c0-e816f1846e55

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
import Theorems.Thm_VariableBound_ArithNat_gPD_le_W
import Theorems.Thm_VariableBound_ArithNat_size_objMax_le
import Theorems.Thm_VariableBound_ArithNat_size_lists_le
import Theorems.Thm_ClauseBound_Alg_TopArith_two_g_div
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_pow_le_n
import Theorems.Thm_ClauseBound_TopN_Arith_lamS_mul_le
import Theorems.Thm_ClauseBound_TopN_Arith_pow_le_n
import Theorems.Thm_ClauseBound_TopN_Arith_size_n_le
import Theorems.Thm_ClauseBound_TopN_Arith_two_g_div
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
import Theorems.Thm_UniformInK_ArithNat_WofU_ge
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
theorem _root_.solution (hB : StBounds) (hβ : 1 ≤ β) (hkb : k ≤ β) (hK : 2 ≤ K) (hn17 : K ^ 17 ≤ n) (hlt : n < K ^ (17 * C₀)) :
    K * (3 * K ^ 8 * K.size) ≤ 3 * (WofU β K * n) ∧
    K * (PbD K n (2 ^ β) * (2 * (3 * K ^ 8) / K + 1)) ≤ 3 * GD C₀ * (WofU β K * n) ∧
    K * ((K - 1) * lamS K (3 * K ^ 8) (UbD k K n (2 ^ β)) (PbD K n (2 ^ β))) ≤ (19 + 140 * k + GD C₀) * (WofU β K * n) ∧
    3 * K ^ 8 * PbD K n (2 ^ β) ≤ GD C₀ * (WofU β K * n) ∧
    K * (18 * K ^ 16) ≤ 18 * (WofU β K * n) ∧
    K * K ^ 2 ≤ WofU β K * n ∧
    K * (C₀ * K ^ 2 * (5 * (17 * C₀ * K.size) + 16)) ≤ C₀ * (85 * C₀ + 16) * (WofU β K * n) ∧
    K * (3 * K ^ 8 * (3 * K ^ 8) * 2 * Nat.size (objMax n (2 ^ β))) ≤ 18 * (4 + 17 * C₀) * (WofU β K * n) ∧
    K * (Nat.size (8 * (10 * n + 1) * (sbMax (2 ^ β) + 1) * (Nat.size (2 ^ β * n) + 2) + 8) + 2 + (β + 5 * k + 10 + (k + 3) * n.size)) ≤
      (10 + 34 * C₀) * (WofU β K * n) := by
  have hK1 : 1 ≤ K := by omega
  obtain ⟨-, -, -, w4, w5, w6, -, w8⟩ := WofU_ge (β := β) hK1
  have hz := size_n_le hlt
  have hY : 1 ≤ K.size := Nat.size_pos.2 hK1
  have hKn : K ≤ n := by simpa using pow_le_n hK1 hn17 (j := 1) (by norm_num)
  have hn0 : 1 ≤ n := hK1.trans hKn
  have gP := gPD_le_W (C₀ := C₀) hB hβ hK hn17 hlt
  have hUb := UbD_le (k := k) (K := K) hB hβ hn0
  have hso := size_objMax_le β n
  have hsl := size_lists_le β n
  obtain ⟨W, hW⟩ : ∃ W, W = WofU β K := ⟨_, rfl⟩
  rw [← hW] at w4 w5 w6 w8 gP ⊢
  obtain ⟨b, hb⟩ : ∃ b, b = β + 3 := ⟨_, rfl⟩
  rw [← hb] at w4 w6
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = K.size := ⟨_, rfl⟩
  rw [← hYd] at w4 w5 hz hY ⊢
  obtain ⟨G, hG⟩ : ∃ G, G = GD C₀ := ⟨_, rfl⟩
  rw [← hG] at gP ⊢
  have hb1 : 1 ≤ b := by omega
  have Wn : n ≤ W * n := Nat.le_mul_of_pos_left _ w8
  have K16 : K * K ^ 16 ≤ n := by rw [← pow_succ']; exact hn17
  have a1 : b ≤ b * Y := Nat.le_mul_of_pos_right _ hY
  have a2 : 17 * C₀ * Y ≤ 17 * C₀ * (b * Y) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hb1)
  have UbW : UbD k K n (2 ^ β) ≤ (140 * k + 18) * (W * n) := by
    have c1 : 140 * k * n * (β + 1) ≤ 140 * k * (W * n) := by
      calc 140 * k * n * (β + 1) = 140 * k * ((β + 1) * n) := by ring
        _ ≤ 140 * k * (W * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ ((by omega : β + 1 ≤ b).trans w6))
    have c2 : 18 * K ^ 16 ≤ 18 * (W * n) := Nat.mul_le_mul_left _ ((pow_le_n hK1 hn17 (by norm_num)).trans Wn)
    calc UbD k K n (2 ^ β) ≤ 140 * k * n * (β + 1) + 18 * K ^ 16 := hUb
      _ ≤ 140 * k * (W * n) + 18 * (W * n) := Nat.add_le_add c1 c2
      _ = (140 * k + 18) * (W * n) := by ring
  refine ⟨?_, ?_, ?_, gP, ?_, ?_, ?_, ?_, ?_⟩
  · calc K * (3 * K ^ 8 * Y) = 3 * (Y * K ^ 9) := by ring
      _ ≤ 3 * (W * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul w5 (pow_le_n hK1 hn17 (by norm_num)))
  · have h1 : K * (2 * (3 * K ^ 8) / K + 1) ≤ 3 * (3 * K ^ 8) := by
      rw [Arith.two_g_div hK1]
      have h7 : K ≤ K ^ 8 := Nat.le_self_pow (by norm_num) K
      have e : K * (6 * K ^ 7 + 1) = 6 * K ^ 8 + K := by ring
      omega
    calc K * (PbD K n (2 ^ β) * (2 * (3 * K ^ 8) / K + 1)) = PbD K n (2 ^ β) * (K * (2 * (3 * K ^ 8) / K + 1)) := by ring
      _ ≤ PbD K n (2 ^ β) * (3 * (3 * K ^ 8)) := Nat.mul_le_mul_left _ h1
      _ = 3 * (3 * K ^ 8 * PbD K n (2 ^ β)) := by ring
      _ ≤ 3 * (G * (W * n)) := Nat.mul_le_mul_left _ gP
      _ = 3 * G * (W * n) := by ring
  · have h1 := lamS_mul_le K (3 * K ^ 8) (UbD k K n (2 ^ β)) (PbD K n (2 ^ β))
    generalize lamS K (3 * K ^ 8) (UbD k K n (2 ^ β)) (PbD K n (2 ^ β)) = lam at h1 ⊢
    have h2 : K * (K ^ 2 * lam) ≤ K * (K ^ 2 + UbD k K n (2 ^ β) + 3 * K ^ 8 * PbD K n (2 ^ β)) := by
      have : 3 * K ^ 8 * PbD K n (2 ^ β) ≤ K * (3 * K ^ 8 * PbD K n (2 ^ β)) := Nat.le_mul_of_pos_left _ hK1
      calc K * (K ^ 2 * lam) = lam * K ^ 3 := by ring
        _ ≤ K ^ 3 + K * UbD k K n (2 ^ β) + 3 * K ^ 8 * PbD K n (2 ^ β) := h1
        _ ≤ K ^ 3 + K * UbD k K n (2 ^ β) + K * (3 * K ^ 8 * PbD K n (2 ^ β)) := Nat.add_le_add_left this _
        _ = K * (K ^ 2 + UbD k K n (2 ^ β) + 3 * K ^ 8 * PbD K n (2 ^ β)) := by ring
    have h3 := Nat.le_of_mul_le_mul_left h2 hK1
    have h4 : K ^ 2 ≤ W * n := (pow_le_n hK1 hn17 (by norm_num)).trans Wn
    calc K * ((K - 1) * lam) ≤ K * (K * lam) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
      _ = K ^ 2 * lam := by ring
      _ ≤ K ^ 2 + UbD k K n (2 ^ β) + 3 * K ^ 8 * PbD K n (2 ^ β) := h3
      _ ≤ W * n + (140 * k + 18) * (W * n) + G * (W * n) := Nat.add_le_add (Nat.add_le_add h4 UbW) gP
      _ = (19 + 140 * k + G) * (W * n) := by ring
  · calc K * (18 * K ^ 16) = 18 * (K * K ^ 16) := by ring
      _ ≤ 18 * (W * n) := Nat.mul_le_mul_left _ (K16.trans Wn)
  · calc K * K ^ 2 = K ^ 3 := by ring
      _ ≤ n := pow_le_n hK1 hn17 (by norm_num)
      _ ≤ W * n := Wn
  · have h1 : 5 * (17 * C₀ * Y) + 16 ≤ (85 * C₀ + 16) * W := by
      calc 5 * (17 * C₀ * Y) + 16 ≤ 85 * C₀ * Y + 16 * Y := by nlinarith
        _ = (85 * C₀ + 16) * Y := by ring
        _ ≤ (85 * C₀ + 16) * W := Nat.mul_le_mul_left _ w5
    calc K * (C₀ * K ^ 2 * (5 * (17 * C₀ * Y) + 16)) = C₀ * ((5 * (17 * C₀ * Y) + 16) * K ^ 3) := by ring
      _ ≤ C₀ * ((85 * C₀ + 16) * W * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 (pow_le_n hK1 hn17 (by norm_num)))
      _ = C₀ * (85 * C₀ + 16) * (W * n) := by ring
  · have h2 : Nat.size (objMax n (2 ^ β)) ≤ (4 + 17 * C₀) * W := by
      calc Nat.size (objMax n (2 ^ β)) ≤ 2 * β + n.size + 10 := hso
        _ ≤ 4 * (b * Y) + 17 * C₀ * (b * Y) := by omega
        _ = (4 + 17 * C₀) * (b * Y) := by ring
        _ ≤ (4 + 17 * C₀) * W := Nat.mul_le_mul_left _ w4
    calc K * (3 * K ^ 8 * (3 * K ^ 8) * 2 * Nat.size (objMax n (2 ^ β))) = 18 * (Nat.size (objMax n (2 ^ β)) * K ^ 17) := by ring
      _ ≤ 18 * ((4 + 17 * C₀) * W * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul h2 hn17)
      _ = 18 * (4 + 17 * C₀) * (W * n) := by ring
  · generalize Nat.size (8 * (10 * n + 1) * (sbMax (2 ^ β) + 1) * (Nat.size (2 ^ β * n) + 2) + 8) = sl at hsl ⊢
    have h1 : sl + 2 + (β + 5 * k + 10 + (k + 3) * n.size) ≤ (10 + 34 * C₀) * (b * Y) := by
      have c1 : (k + 5) * n.size ≤ 2 * b * (17 * C₀ * Y) := Nat.mul_le_mul (by omega) hz
      have e1 : (k + 3) * n.size + 2 * n.size = (k + 5) * n.size := by ring
      have c2 : 4 * β + 5 * k + 29 ≤ 10 * b := by omega
      calc sl + 2 + (β + 5 * k + 10 + (k + 3) * n.size) ≤ (4 * β + 5 * k + 29) + (k + 5) * n.size := by omega
        _ ≤ 10 * b + 2 * b * (17 * C₀ * Y) := Nat.add_le_add c2 c1
        _ ≤ 10 * (b * Y) + 2 * b * (17 * C₀ * Y) := Nat.add_le_add_right (Nat.mul_le_mul_left _ a1) _
        _ = (10 + 34 * C₀) * (b * Y) := by ring
    calc K * (sl + 2 + (β + 5 * k + 10 + (k + 3) * n.size)) ≤ n * ((10 + 34 * C₀) * (b * Y)) := Nat.mul_le_mul hKn h1
      _ = (10 + 34 * C₀) * (b * Y * n) := by ring
      _ ≤ (10 + 34 * C₀) * (W * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ w4)
end VariableBound.ArithNat

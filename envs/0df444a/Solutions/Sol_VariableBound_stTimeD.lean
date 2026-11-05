-- Prove2me | solution 1 for VariableBound.stTimeD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:30:12.583909+00:00
-- url     : https://prove2.me/submissions/a91aa7fb-9aae-45cc-8d56-0da822ec66be

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_Defs
import Definitions.Def_UniformInK_Top_Time
import Definitions.Def_ClauseBound_TopN_End
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_VariableBound_Top_Time
import Theorems.Thm_ClauseBound_Alg_End_length_enc_succ_le
import Theorems.Thm_ClauseBound_Alg_End_log_le_self
import Theorems.Thm_ClauseBound_Alg_End_one_le_log
import Theorems.Thm_ClauseBound_Alg_End_one_le_mul_of_div_le
import Theorems.Thm_ClauseBound_TopN_End_log_le_mul
import Theorems.Thm_Groundwork_DecodeK_length_enc_succ_le
import Theorems.Thm_Groundwork_Decode_length_enc_succ_le
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
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
import Theorems.Thm_P2M_ClauseBound_TopN_End_time_le__345fca42d669
import Theorems.Thm_UniformInK_Time_length_enc_succ_le
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
open VariableBound
open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Alg.End ClauseBound.TopN ClauseBound.TopN.End UniformInK
namespace VariableBound
theorem _root_.solution (hA : StArithD) (hP : StPlanLeD) (hD : StDecM) : StTimeD := by
  intro Idx _ S e C₀ Q hS slU C h1 h2 r c₁ hr he hF q
  set K₀ := S.K (Q.idx 0) with hK₀
  obtain ⟨A, B, hA⟩ := hA Idx S e C₀ Q hS slU C h1 h2
  obtain ⟨c₂, hF⟩ := hF B
  -- c₁ ≥ 1, because e is positive
  have hc : 1 ≤ c₁ := by
    rcases Nat.eq_zero_or_pos c₁ with h0 | h0
    · exfalso
      have g1 := he (K₀ ^ 17) le_rfl
      have g2 := Q.e_ge (Q.pick (root17 (K₀ ^ 17))).1.length
      have g3 : (2 : ℝ) ≤ S.K (Q.idx (Q.pick (root17 (K₀ ^ 17))).1.length) := by exact_mod_cast Q.K_two _
      have g4 : 0 < Real.logb 2 (S.K (Q.idx (Q.pick (root17 (K₀ ^ 17))).1.length)) := Real.logb_pos (by norm_num) (by linarith)
      have g5 : 0 < 1 / Real.logb 2 (S.K (Q.idx (Q.pick (root17 (K₀ ^ 17))).1.length)) ^ C₀ := by positivity
      have g6 : 0 < e (Q.pick (root17 (K₀ ^ 17))).1.length * (((slU (Q.pick (root17 (K₀ ^ 17))).1).length : ℝ) + 1) := by
        have : 0 < e (Q.pick (root17 (K₀ ^ 17))).1.length := lt_of_lt_of_le g5 g2
        positivity
      rw [h0] at g1
      simp only [Nat.cast_zero, zero_mul] at g1
      linarith
    · exact h0
  set D : ℕ := c₁ * (3 * (c₁ + 1).factorial * 2 ^ (c₁ + 1))
  set H : ℕ := 5 * D
  set G₀ : ℕ := c₁ * (K₀ ^ 17 + 2) ^ c₁
  set G : ℕ := A * c₁ + G₀ + c₂
  refine ⟨q * (1 + 1) ^ q + q * (H + G), fun k n φ hk hn1 hφ => ?_⟩
  obtain ⟨hdk, hdf⟩ := hD k n φ hk hφ.1
  have hkU : kU (SatM.enc k φ) = k := by rw [kU, hdk, List.length_replicate]
  have hnU : nU (SatM.enc k φ) = n := by rw [nU, hdf, List.length_replicate]
  have heq : eD S Q.pick slU (SatM.enc k φ) = (planAtD S k n (Q.pick (root17 n)).2 (slU (Q.pick (root17 n)).1).length).getD n := by
    rw [eD, planD, idxU, precU, hkU, hnU]
  have hEn : eD S Q.pick slU (SatM.enc k φ) ≤ n := heq ▸ hP Idx S k n _ _
  have hlen := Time.length_enc_succ_le hk hφ
  unfold SatM.boundNK
  refine Nat.le_floor ?_
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ hk'
  have hkk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hrn := hr n hn1
  have hr0 : 0 ≤ r n := le_trans (by have := one_le_log n; positivity) hrn
  have hY : 0 ≤ (n : ℝ) * r n := by positivity
  have hX : 0 ≤ (k : ℝ) ^ 2 * ((n : ℝ) * r n) := by positivity
  have hYX : (n : ℝ) * r n ≤ (k : ℝ) ^ 2 * ((n : ℝ) * r n) := le_mul_of_one_le_left hY hk2
  -- the length of the code
  have hlog := log_le_mul hc hn1 hrn
  have hL : (((SatM.enc k φ).length + 1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) * (2 : ℝ) ^ ((H : ℝ) * ((k : ℝ) ^ 2 * ((n : ℝ) * r n))) := by
    have p0 : (n : ℝ) + 2 = (2 : ℝ) ^ Real.logb 2 ((n : ℝ) + 2) := (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
    calc (((SatM.enc k φ).length + 1 : ℕ) : ℝ) ≤ (((n + 2) ^ (5 * k) : ℕ) : ℝ) := by exact_mod_cast hlen
      _ = ((n : ℝ) + 2) ^ (5 * k) := by push_cast; ring
      _ = ((2 : ℝ) ^ Real.logb 2 ((n : ℝ) + 2)) ^ (5 * k) := by rw [← p0]
      _ = (2 : ℝ) ^ (Real.logb 2 ((n : ℝ) + 2) * ((5 * k : ℕ) : ℝ)) := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      _ ≤ (2 : ℝ) ^ ((H : ℝ) * ((k : ℝ) ^ 2 * ((n : ℝ) * r n))) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          calc Real.logb 2 ((n : ℝ) + 2) * ((5 * k : ℕ) : ℝ) ≤ ((D : ℕ) : ℝ) * ((n : ℝ) * r n) * ((5 * k : ℕ) : ℝ) :=
                mul_le_mul_of_nonneg_right hlog (by positivity)
            _ = (H : ℝ) * ((n : ℝ) * r n) * (k : ℝ) := by simp only [H]; push_cast; ring
            _ ≤ (H : ℝ) * ((n : ℝ) * r n) * (k : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hkk (by positivity)
            _ = (H : ℝ) * ((k : ℝ) ^ 2 * ((n : ℝ) * r n)) := by ring
      _ = _ := by rw [Nat.cast_one, one_mul]
  -- the exponent
  have hE : (eD S Q.pick slU (SatM.enc k φ) : ℝ) ≤ (G : ℝ) * ((k : ℝ) ^ 2 * ((n : ℝ) * r n)) := by
    have hGa : ((A * c₁ : ℕ) : ℝ) * ((k : ℝ) ^ 2 * ((n : ℝ) * r n)) ≤ (G : ℝ) * ((k : ℝ) ^ 2 * ((n : ℝ) * r n)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (show A * c₁ ≤ G by simp only [G]; omega)) hX
    have hGb : ((G₀ : ℕ) : ℝ) * ((k : ℝ) ^ 2 * ((n : ℝ) * r n)) ≤ (G : ℝ) * ((k : ℝ) ^ 2 * ((n : ℝ) * r n)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (show G₀ ≤ G by simp only [G]; omega)) hX
    have hGc : ((c₂ : ℕ) : ℝ) * ((k : ℝ) ^ 2 * ((n : ℝ) * r n)) ≤ (G : ℝ) * ((k : ℝ) ^ 2 * ((n : ℝ) * r n)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (show c₂ ≤ G by simp only [G]; omega)) hX
    by_cases hs : n < K₀ ^ 17
    · refine le_trans ?_ hGb
      have g1 := one_le_mul_of_div_le hc (one_le_log n) hrn
      have g2 : Real.logb 2 ((n : ℝ) + 2) ≤ ((K₀ ^ 17 + 2 : ℕ) : ℝ) := by
        refine (log_le_self n).trans ?_
        have : n + 2 ≤ K₀ ^ 17 + 2 := by omega
        exact_mod_cast this
      have g3 : Real.logb 2 ((n : ℝ) + 2) ^ c₁ ≤ ((K₀ ^ 17 + 2 : ℕ) : ℝ) ^ c₁ := pow_le_pow_left₀ (by linarith [one_le_log n]) g2 _
      have g4 : 1 ≤ ((G₀ : ℕ) : ℝ) * r n := by
        refine g1.trans (mul_le_mul_of_nonneg_right ?_ hr0)
        simp only [G₀]
        rw [Nat.cast_mul, Nat.cast_pow]
        exact mul_le_mul_of_nonneg_left g3 (by positivity)
      calc (eD S Q.pick slU (SatM.enc k φ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hEn
        _ = (n : ℝ) * 1 := (mul_one _).symm
        _ ≤ (n : ℝ) * (((G₀ : ℕ) : ℝ) * r n) := mul_le_mul_of_nonneg_left g4 (by positivity)
        _ = ((G₀ : ℕ) : ℝ) * ((n : ℝ) * r n) := by ring
        _ ≤ ((G₀ : ℕ) : ℝ) * ((k : ℝ) ^ 2 * ((n : ℝ) * r n)) := mul_le_mul_of_nonneg_left hYX (by positivity)
    · rcases hA k n hk (not_lt.1 hs) with g1 | g1
      · refine le_trans ?_ hGa
        have g2 := he n (not_lt.1 hs)
        rw [heq]
        calc _ ≤ A * (k : ℝ) ^ 2 * n * e (Q.pick (root17 n)).1.length * (((slU (Q.pick (root17 n)).1).length : ℝ) + 1) := g1
          _ = A * (k : ℝ) ^ 2 * n * (e (Q.pick (root17 n)).1.length * (((slU (Q.pick (root17 n)).1).length : ℝ) + 1)) := by ring
          _ ≤ A * (k : ℝ) ^ 2 * n * (c₁ * r n) := mul_le_mul_of_nonneg_left g2 (by positivity)
          _ = _ := by push_cast; ring
      · refine le_trans ?_ hGc
        have g2 := hF k n hk hn1 g1
        calc (eD S Q.pick slU (SatM.enc k φ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hEn
          _ = (n : ℝ) * 1 := (mul_one _).symm
          _ ≤ (n : ℝ) * ((c₂ : ℝ) * (k : ℝ) ^ 2 * r n) := mul_le_mul_of_nonneg_left g2 (by positivity)
          _ = _ := by ring
  have ht := time_le' q (SatM.enc k φ).length (eD S Q.pick slU (SatM.enc k φ)) 1 H G hX hL hE
  refine ht.trans (le_of_eq ?_)
  congr 2
  ring
end VariableBound

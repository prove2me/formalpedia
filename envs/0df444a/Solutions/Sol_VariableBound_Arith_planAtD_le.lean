-- Prove2me | solution 1 for VariableBound.Arith.planAtD_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:49:22.793195+00:00
-- url     : https://prove2.me/submissions/49380676-7c03-487a-b2ef-f73cb3c77886

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_ArithDefs
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_UniformInK_Top_ArithTop
import Definitions.Def_UniformInK_Top_ArithTop
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Top_ArithTop
import Theorems.Thm_VariableBound_Arith_const_le
import Theorems.Thm_VariableBound_Arith_of_BkD
import Theorems.Thm_VariableBound_Arith_test3
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_pow_le_n
import Theorems.Thm_ClauseBound_TopN_Arith_le_of_small
import Theorems.Thm_ClauseBound_TopN_Arith_pow_le_n
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
import Theorems.Thm_UniformInK_Arith_two_pow_s0U_le
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
open VariableBound VariableBound.Arith
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks UniformInK UniformInK.Arith
namespace VariableBound.Arith
theorem _root_.solution (hN : StNeedD) (hP : StPlanLeD) (hPN : StPlanNeedD) (hM : StMasterU) (hDL : StDLogU) (h6 : StSixU) (hB : StBetaU)
    {Idx : Type} [Enc Idx] {S : Solver Idx} (hS : S.Poly) (i : Idx) {e : ℝ} {C C₀ k n s : ℕ} (hk : 1 ≤ k) (hK : 2 ≤ S.K i) (hn17 : S.K i ^ 17 ≤ n)
    (hlt : n < S.K i ^ (17 * C₀)) (he1 : e ≤ 1) (hs : 1 / (2 : ℝ) ^ s ≤ e) (heK : 1 / Real.logb 2 (S.K i) ^ C₀ ≤ e) (h2 : (2 : ℝ) ^ s ≤ (2 / e) ^ C)
    (hrate : ∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
      e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B)))
    (hBk : BkD C C₀ * k ^ 2 ≤ Nat.log 2 n) :
    (((planAtD S k n i s).getD n : ℕ) : ℝ) ≤ (AexpD C₀ : ℝ) * (k : ℝ) ^ 2 * n * e * ((s : ℝ) + 1) := by
  have pn : (((planAtD S k n i s).getD n : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hP Idx S k n i s
  have hK1 : 1 ≤ S.K i := by omega
  have hKn : S.K i ≤ n := by simpa using pow_le_n hK1 hn17 (j := 1) (by norm_num)
  have hn1 : 1 ≤ n := hK1.trans hKn
  have he0 : 0 < e := lt_of_lt_of_le (by positivity) hs
  have hq : (1 : ℝ) ≤ (s : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    linarith
  have hne : 0 ≤ (n : ℝ) * e := mul_nonneg (Nat.cast_nonneg n) he0.le
  have hneq : (n : ℝ) * e ≤ (n : ℝ) * e * ((s : ℝ) + 1) := le_mul_of_one_le_right hne hq
  obtain ⟨-, hbD, -⟩ := hB k s hk
  have t6 := of_BkD hBk
  have ha1 : 1 ≤ aU C C₀ * k := Nat.mul_pos (by unfold aU; omega) hk
  have t4 := hDL (S.K i) n s C C₀ k e hK hKn heK h2
  have hsix := h6 (2 ^ betaU k s) (aU C C₀ * k) (S.K i) n C₀ ha1 hn1 hlt t4 t6
  have hMas := hM (betaU k s) (S.K i) C₀ e hbD hK heK hsix
  have t2 : 2 ^ betaU k s ≤ n + 1 := ((Nat.le_self_pow (by norm_num) _).trans (hsix.trans hKn)).trans (Nat.le_succ n)
  have t3 : 29 * LD (2 ^ betaU k s) + 19 ≤ n := test3 hbD (hsix.trans hKn)
  have hk2 : (0 : ℝ) ≤ (k : ℝ) ^ 2 := by positivity
  have hT : 0 ≤ (k : ℝ) ^ 2 * ((n : ℝ) * e * ((s : ℝ) + 1)) := mul_nonneg hk2 (hne.trans hneq)
  have eA : (AexpD C₀ : ℝ) * (k : ℝ) ^ 2 * n * e * ((s : ℝ) + 1) =
      ((140 * 35 + (ccD 0 C₀ + 140) * A1U C₀ + 1 : ℕ) : ℝ) * ((k : ℝ) ^ 2 * ((n : ℝ) * e * ((s : ℝ) + 1))) + 4 * ((k : ℝ) ^ 2 * ((n : ℝ) * e * ((s : ℝ) + 1))) := by
    unfold AexpD; push_cast; ring
  rw [eA]
  by_cases c1 : s0U k ≤ s
  · have h3 : (((planAtD S k n i s).getD n : ℕ) : ℝ) ≤ (needD S k i n s : ℝ) := by
      exact_mod_cast hPN Idx S hS k n i s c1 t2 t3
    have h4 := hN Idx S i e C₀ k n s (A1U C₀) hk hK hn17 hlt t2 he0 he1 hs hMas hrate
    have h5 : ((140 * k * (35 * k) + ccD k C₀ * A1U C₀ + 1 : ℕ) : ℝ) ≤ ((140 * 35 + (ccD 0 C₀ + 140) * A1U C₀ + 1 : ℕ) : ℝ) * (k : ℝ) ^ 2 := by
      exact_mod_cast const_le hk C₀ (A1U C₀)
    have h6' := mul_le_mul_of_nonneg_right h5 (hne.trans hneq)
    have e2 : ((140 * k * (35 * k) + ccD k C₀ * A1U C₀ + 1 : ℕ) : ℝ) * n * e * ((s : ℝ) + 1) =
        ((140 * k * (35 * k) + ccD k C₀ * A1U C₀ + 1 : ℕ) : ℝ) * ((n : ℝ) * e * ((s : ℝ) + 1)) := by ring
    rw [e2] at h4
    have e3 : ((140 * 35 + (ccD 0 C₀ + 140) * A1U C₀ + 1 : ℕ) : ℝ) * (k : ℝ) ^ 2 * ((n : ℝ) * e * ((s : ℝ) + 1)) =
        ((140 * 35 + (ccD 0 C₀ + 140) * A1U C₀ + 1 : ℕ) : ℝ) * ((k : ℝ) ^ 2 * ((n : ℝ) * e * ((s : ℝ) + 1))) := by ring
    rw [e3] at h6'
    linarith
  · have h3 := le_of_small (n := n) (not_le.1 c1).le hs
    have h4 : ((2 ^ s0U k : ℕ) : ℝ) ≤ 4 * (k : ℝ) ^ 2 := by exact_mod_cast two_pow_s0U_le hk
    have h5 := mul_le_mul_of_nonneg_right h4 hne
    have h6' : 4 * (k : ℝ) ^ 2 * ((n : ℝ) * e) ≤ 4 * (k : ℝ) ^ 2 * ((n : ℝ) * e * ((s : ℝ) + 1)) := mul_le_mul_of_nonneg_left hneq (by positivity)
    have h7 : 0 ≤ ((140 * 35 + (ccD 0 C₀ + 140) * A1U C₀ + 1 : ℕ) : ℝ) * ((k : ℝ) ^ 2 * ((n : ℝ) * e * ((s : ℝ) + 1))) := mul_nonneg (Nat.cast_nonneg _) hT
    have e4 : 4 * (k : ℝ) ^ 2 * ((n : ℝ) * e * ((s : ℝ) + 1)) = 4 * ((k : ℝ) ^ 2 * ((n : ℝ) * e * ((s : ℝ) + 1))) := by ring
    linarith
end VariableBound.Arith

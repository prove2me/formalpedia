-- Prove2me | solution 1 for RecursionToBound.needAt_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:25:52.435106+00:00
-- url     : https://prove2.me/submissions/0f3f9d6f-4c72-420d-bdb6-dedeabdf13f9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_VariableBound_Top_ArithDefs
import Definitions.Def_RecursionToBound_Numbers
import Definitions.Def_VariableBound_Top_ArithNat
import Definitions.Def_UniformInK_Top_ArithMaster
import Definitions.Def_VariableBound_Net_Main
import Definitions.Def_VariableBound_Net_StepCost
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Definitions.Def_RecursionToBound_OneOutput
import Theorems.Thm_RecursionToBound_real_core
import Theorems.Thm_RecursionToBound_lamS_mono
import Theorems.Thm_RecursionToBound_bitsS_mono
import Theorems.Thm_RecursionToBound_needAt_le_sum
import Theorems.Thm_ClauseBound_Alg_TopArith_logb_le_of_le_pow
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_RecursionToBound_boundsGrowWithDelta
import Theorems.Thm_VariableBound_ArithNat_bitsS_eq
import Theorems.Thm_VariableBound_Net_Main_bounds
import Theorems.Thm_VariableBound_Net_Main_size
import Theorems.Thm_VariableBound_Net_StepCost_bitsS_eq
import Theorems.Thm_VariableBound_stArgD
import Theorems.Thm_VariableBound_stLowerD
import Theorems.Thm_VariableBound_stUbD


set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.ParityChecks UniformInK VariableBound.Net MainTheoremForms VariableBound.Paper
namespace RecursionToBound
theorem _root_.solution {Idx : Type} [Enc Idx] (S : Solver Idx) (i : Idx) {e : ℝ} {C₀ k n Δ β₁ β A₁ : ℕ}
    (hK : 2 ≤ S.K i) (hn17 : S.K i ^ 17 ≤ n) (hlt : n < S.K i ^ (17 * C₀))
    (hβ₁ : 1 ≤ β₁) (hΔ : Δ ≤ 2 ^ β₁) (hββ : β₁ ≤ β) (hkβ : k ≤ β) (hbD : β + 3 ≤ 2 ^ β) (hD : 2 ^ β ≤ n + 1)
    (he0 : 0 < e) (he1 : e ≤ 1) (hM : ((WofU β (S.K i) : ℕ) : ℝ) ≤ (A₁ : ℝ) * (S.K i) * e)
    (hrate : ∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
      e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B))) :
    (needAt S k i n Δ : ℝ) ≤ e * (140 * (k : ℝ) * n * ((β₁ + 1 : ℕ) : ℝ)) + ((VariableBound.ccD k C₀ * A₁ : ℕ) : ℝ) * ((n : ℝ) * e) := by
  have hB := VariableBound.Net.Main.bounds
  have hsum := needAt_le_sum S i k n (hΔ.trans (Nat.pow_le_pow_right (by norm_num) hββ))
  obtain ⟨K, hKdef⟩ : ∃ K, K = S.K i := ⟨_, rfl⟩
  rw [← hKdef] at hK hn17 hlt hM hrate hsum
  have hΔD : Δ ≤ 2 ^ β := hΔ.trans (Nat.pow_le_pow_right (by norm_num) hββ)
  have hβ1 : 1 ≤ β := hβ₁.trans hββ
  have hK1 : 1 ≤ K := by omega
  have hKn : K ≤ n := (Nat.le_self_pow (by norm_num) K).trans hn17
  have hn1 : 1 ≤ n := hK1.trans hKn
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9⟩ := VariableBound.stLowerD hB β k K n C₀ hβ1 hkβ hK hn17 hlt
  have harg := VariableBound.stArgD hB β k K n C₀ hkβ hbD hK hn17 hlt hD
  have hUb := VariableBound.stUbD hB β₁ k K n hβ₁ hn1
  obtain ⟨hU1, -, -, -⟩ := boundsGrowWithDelta k K n Δ (2 ^ β₁) hΔ
  obtain ⟨hU2, hP2, -, -⟩ := boundsGrowWithDelta k K n Δ (2 ^ β) hΔD
  have hlam1 : 1 ≤ lamS K (3 * K ^ 8) (UbD k K n Δ) (PbD K n Δ) := by
    unfold lamS
    rw [Nat.le_div_iff_mul_le (by positivity)]
    omega
  have hB1 : 1 ≤ bitsS K (3 * K ^ 8) (PbD K n Δ) (BbD k n) := by
    rw [StepCost.bitsS_eq hK1]
    have b1 : 1 ≤ BbD k n := by unfold BbD BD; omega
    have b2 : 1 ≤ 6 * K ^ 8 + 36 * K ^ 15 := Nat.add_pos_left (by positivity) _
    exact (Nat.mul_pos b2 b1).trans_le (Nat.le_add_left _ _)
  have hlamK : lamS K (3 * K ^ 8) (UbD k K n Δ) (PbD K n Δ) * K ^ 3 ≤ K ^ 3 + K * UbD k K n (2 ^ β₁) + 3 * K ^ 8 * PbD K n (2 ^ β) :=
    (Nat.div_mul_le_self _ _).trans (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left K hU1) _) (Nat.mul_le_mul_left _ hP2))
  have harg' : K * (lamS K (3 * K ^ 8) (UbD k K n Δ) (PbD K n Δ) + bitsS K (3 * K ^ 8) (PbD K n Δ) (BbD k n)) ≤ 2 ^ (5 * (17 * C₀ * K.size) + 16) :=
    (Nat.mul_le_mul_left K (Nat.add_le_add (lamS_mono _ _ hU2 hP2) (bitsS_mono _ _ _ hP2))).trans harg
  have hr := hrate _ _ hlam1 hB1
  have hlog : Real.logb 2 ((K : ℝ) * ((lamS K (3 * K ^ 8) (UbD k K n Δ) (PbD K n Δ) : ℝ) + (bitsS K (3 * K ^ 8) (PbD K n Δ) (BbD k n) : ℝ))) ≤
      ((5 * (17 * C₀ * K.size) + 16 : ℕ) : ℝ) := by
    have h := logb_le_of_le_pow _ _ (Nat.mul_pos hK1 (Nat.add_pos_left hlam1 _)) harg'
    push_cast at h ⊢
    exact h
  generalize S.need (i, List.replicate (lamS K (3 * K ^ 8) (UbD k K n Δ) (PbD K n Δ)) (), List.replicate (bitsS K (3 * K ^ 8) (PbD K n Δ) (BbD k n)) ()) = nd at hr hsum
  generalize bitsS K (3 * K ^ 8) (PbD K n Δ) (BbD k n) = Bt at hr hlog
  generalize lamS K (3 * K ^ 8) (UbD k K n Δ) (PbD K n Δ) = lam at hr hlog hlamK
  have o9' : K * (Nat.size (8 * (10 * n + 1) * (sbMax (2 ^ β) + 1) * (Nat.size (2 ^ β * n) + 2) + 8) + 1) ≤ (10 + 34 * C₀) * (WofU β K * n) :=
    (Nat.mul_le_mul_left K (by omega)).trans o9
  have r1 : (K : ℝ) * ((3 * K ^ 8 * K.size : ℕ) : ℝ) ≤ 3 * (((WofU β K : ℕ) : ℝ) * n) := by exact_mod_cast o1
  have r2 : (K : ℝ) * ((PbD K n (2 ^ β) * (2 * (3 * K ^ 8) / K + 1) : ℕ) : ℝ) ≤ ((3 * VariableBound.GD C₀ : ℕ) : ℝ) * (((WofU β K : ℕ) : ℝ) * n) := by exact_mod_cast o2
  have r3 : (K : ℝ) * (((K - 1) * lamS K (3 * K ^ 8) (UbD k K n (2 ^ β)) (PbD K n (2 ^ β)) : ℕ) : ℝ) ≤ ((19 + 140 * k + VariableBound.GD C₀ : ℕ) : ℝ) * (((WofU β K : ℕ) : ℝ) * n) := by
    exact_mod_cast o3
  have r4 : ((3 * K ^ 8 * PbD K n (2 ^ β) : ℕ) : ℝ) ≤ (VariableBound.GD C₀ : ℝ) * (((WofU β K : ℕ) : ℝ) * n) := by exact_mod_cast o4
  have r5 : (K : ℝ) * ((18 * K ^ 16 : ℕ) : ℝ) ≤ 18 * (((WofU β K : ℕ) : ℝ) * n) := by exact_mod_cast o5
  have r6 : (K : ℝ) * (K : ℝ) ^ 2 ≤ ((WofU β K : ℕ) : ℝ) * n := by exact_mod_cast o6
  have r7 : (K : ℝ) * ((C₀ : ℝ) * (K : ℝ) ^ 2 * ((5 * (17 * C₀ * K.size) + 16 : ℕ) : ℝ)) ≤ ((C₀ * (85 * C₀ + 16) : ℕ) : ℝ) * (((WofU β K : ℕ) : ℝ) * n) := by exact_mod_cast o7
  have r8 : (K : ℝ) * ((3 * K ^ 8 * (3 * K ^ 8) * 2 * Nat.size (objMax n (2 ^ β)) : ℕ) : ℝ) ≤ ((18 * (4 + 17 * C₀) : ℕ) : ℝ) * (((WofU β K : ℕ) : ℝ) * n) := by exact_mod_cast o8
  have r9 : (K : ℝ) * ((Nat.size (8 * (10 * n + 1) * (sbMax (2 ^ β) + 1) * (Nat.size (2 ^ β * n) + 2) + 8) + 1 : ℕ) : ℝ) ≤ ((10 + 34 * C₀ : ℕ) : ℝ) * (((WofU β K : ℕ) : ℝ) * n) := by
    exact_mod_cast o9'
  have rU : ((UbD k K n (2 ^ β₁) : ℕ) : ℝ) ≤ 140 * (k : ℝ) * n * ((β₁ + 1 : ℕ) : ℝ) + ((18 * K ^ 16 : ℕ) : ℝ) := by exact_mod_cast hUb
  have rL : (lam : ℝ) * (K : ℝ) ^ 3 ≤ (K : ℝ) ^ 3 + (K : ℝ) * ((UbD k K n (2 ^ β₁) : ℕ) : ℝ) + ((3 * K ^ 8 * PbD K n (2 ^ β) : ℕ) : ℝ) := by exact_mod_cast hlamK
  have rS : (needAt S k i n Δ : ℝ) ≤ ((3 * K ^ 8 * K.size : ℕ) : ℝ) + ((PbD K n (2 ^ β) * (2 * (3 * K ^ 8) / K + 1) : ℕ) : ℝ) +
      (((K - 1) * lamS K (3 * K ^ 8) (UbD k K n (2 ^ β)) (PbD K n (2 ^ β)) : ℕ) : ℝ) + (nd : ℝ) + ((3 * K ^ 8 * (3 * K ^ 8) * 2 * Nat.size (objMax n (2 ^ β)) : ℕ) : ℝ) +
      ((Nat.size (8 * (10 * n + 1) * (sbMax (2 ^ β) + 1) * (Nat.size (2 ^ β * n) + 2) + 8) + 1 : ℕ) : ℝ) := by
    exact_mod_cast hsum
  have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have core := real_core (A := (A₁ : ℝ)) hKr he0 he1 (Nat.cast_nonneg n) (Nat.cast_nonneg C₀) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by norm_num) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by norm_num) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hM r1 r2 r3 r4 r5 r6 r7 r8 r9 rU rL hr hlog
  have ecc : (3 + ((3 * VariableBound.GD C₀ : ℕ) : ℝ) + ((19 + 140 * k + VariableBound.GD C₀ : ℕ) : ℝ) + (VariableBound.GD C₀ : ℝ) + 18 + 1 + ((C₀ * (85 * C₀ + 16) : ℕ) : ℝ) + ((18 * (4 + 17 * C₀) : ℕ) : ℝ) +
      ((10 + 34 * C₀ : ℕ) : ℝ)) * (A₁ : ℝ) = ((VariableBound.ccD k C₀ * A₁ : ℕ) : ℝ) := by
    unfold VariableBound.ccD; push_cast; ring
  rw [ecc] at core
  exact rS.trans core
end RecursionToBound

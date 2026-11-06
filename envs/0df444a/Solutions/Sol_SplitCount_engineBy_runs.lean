-- Prove2me | solution 1 for SplitCount.engineBy_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:03:10.630188+00:00
-- url     : https://prove2.me/submissions/7e412e4b-43c8-4766-8fed-7157c3a14bd3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_SplitCount_Leaf
import Definitions.Def_CountKSat_Walk
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_SplitCount_Suffices
import Theorems.Thm_SplitCount_hasNil_iff
import Theorems.Thm_CountKSat_CountTop_outW_eq
import Theorems.Thm_CountKSat_stWalkSum
import Theorems.Thm_GraphProblems_cntN_le
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Prog_SatTopK_size_fml_le
import Theorems.Thm_Groundwork_Prog_size_nat_le
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_bind_runs
import Theorems.Thm_Groundwork_Stepped_const_runs
import Theorems.Thm_Groundwork_Stepped_ite_runs_false
import Theorems.Thm_Groundwork_Stepped_ite_runs_true
import Theorems.Thm_Groundwork_Stepped_ofFun_runs
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
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
import Theorems.Thm_Groundwork_Unary_const
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
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
import Theorems.Thm_SplitCount_clause_bound
import Theorems.Thm_SplitCount_cntN_le
import Theorems.Thm_SplitCount_cntN_of_nil
import Theorems.Thm_SplitCount_leaf_runs
import Theorems.Thm_SplitCount_outW_eq
import Theorems.Thm_SplitCount_poly_le
import Theorems.Thm_SplitCount_size_binary
import Theorems.Thm_SplitCount_size_fml_le
import Theorems.Thm_SplitCount_size_nat_le
import Theorems.Thm_SplitCount_size_unary
import Theorems.Thm_SplitCount_stack_size
import Theorems.Thm_WidthK_InvK_step
attribute [local fun_prop] Groundwork.PolyT.const
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
open SplitCount
open Groundwork Groundwork.Prog Groundwork.Sparsify Paper CountKSat Eight Eight.Width Occ
namespace SplitCount
theorem _root_.solution {k : ℕ} {δ : ℝ} (hδ : 0 < δ) {step : CNode → Option (CNode × CNode)} {Dd Bl Sk : ℕ} (hsp : SparsifiesPlain k (δ / 3) step Dd Bl Sk)
    {D : StepMachine (List Unit × Fml) ℕ} {δ' : ℝ} {A : ℕ} (hδ' : 0 ≤ δ') (hδB : δ' * ((1 + 3 * (((max k 3 : ℕ) : ℝ) - 3)) * ((Bl : ℝ) + 1)) ≤ δ / 3) (hD : CountsThree D δ' A) :
    ∃ c : ℕ, ∀ (n : ℕ) (ψ : Fml) (M : ℕ), (∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) → n ≤ M → ψ.length ≤ M → 1 ≤ M →
      ∃ T : ℕ, (engineBy step D).Runs (List.replicate n (), ψ) T (c * M ^ c) (SatK.binary n (cntN n ψ)) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n) := by
  obtain ⟨P₁, hP₁⟩ : ∃ P₁, P₁ = leafConst k Bl := ⟨_, rfl⟩
  obtain ⟨P₂, hP₂⟩ : ∃ P₂, P₂ = stackConst k Dd Sk := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 4 * max k 2 + 2 := ⟨_, rfl⟩
  obtain ⟨B₀, hB₀⟩ : ∃ B₀, B₀ = P₂ + 2 * (Q + 4) + 12 := ⟨_, rfl⟩
  refine ⟨B₀ + 3 + A * P₁ ^ A + 2 * A, fun n ψ M hψ hn hm h1 => ?_⟩
  obtain ⟨a, ha⟩ : ∃ a : List Unit × Fml, a = (List.replicate n (), ψ) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = cntN n ψ := ⟨_, rfl⟩
  rw [← ha, ← hv]
  have hv2 : v < 2 ^ (n + 1) := hv ▸ (cntN_le n ψ).trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hM2 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) M
  have h1M2 : 1 ≤ M ^ 2 := Nat.one_le_pow _ _ h1
  have hM23 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right h1 (by norm_num)
  have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
  have hE1 : (1 : ℝ) ≤ (2 : ℝ) ^ (δ * n) := Real.one_le_rpow one_le_two (by positivity)
  have hsa : size a ≤ (Q + 4) * M ^ 2 := by
    have s1 := size_unary n
    have s2 := size_fml_le (k := max k 2) hm fun C hC => ⟨(hψ C hC).1.trans (le_max_left _ _), (hψ C hC).2⟩
    have s3 : M * (max k 2 * (n + 2 + 1) + 1 + 1) ≤ Q * M ^ 2 := by
      calc M * (max k 2 * (n + 2 + 1) + 1 + 1) ≤ M * (Q * M) := Nat.mul_le_mul_left _ (hQ ▸ clause_bound hn h1)
        _ = Q * M ^ 2 := by ring
    have s4 : (Q + 4) * M ^ 2 = Q * M ^ 2 + 4 * M ^ 2 := by ring
    rw [ha, size_prod]
    show size (List.replicate n ()) + size ψ ≤ _
    omega
  -- the count, before it is written in binary
  have main : ∃ T S : ℕ, (Stepped.ite (fun p : List Unit × Fml => hasNil p.2) (Stepped.const 0)
      (walkSum (stepPlain step) rootPlain (Stepped.mapIn leafPlain (Stepped.mapIn widthP D)))).Runs a T S v ∧
      S ≤ P₂ * M ^ 3 + A * (P₁ * M ^ 2) ^ A + (Q + 4) * M ^ 2 + M + 10 ∧ (T : ℝ) ≤ ((A : ℝ) + 2) * (2 : ℝ) ^ (δ * n) := by
    by_cases hnil : [] ∈ ψ
    · refine ⟨1, _, Stepped.ite_runs_true (by rw [ha]; exact (hasNil_iff ψ).2 hnil) (by rw [hv, cntN_of_nil hnil]; exact Stepped.const_runs 0 a), ?_, ?_⟩
      · have : size (0 : ℕ) = 1 := by simp
        rw [this]
        omega
      · push_cast
        nlinarith
    · have hψne : ∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n := by
        intro C hC
        refine ⟨?_, hψ C hC⟩
        rintro rfl
        exact hnil hC
      -- the sparsification for counting
      obtain ⟨t1, t2, t3, t4⟩ := hsp n ψ hψne
      rw [← ha] at t1 t2 t3 t4
      obtain ⟨L, hL⟩ : ∃ L, L = leaves (stepPlain step) (Dd * n) (rootPlain a) := ⟨_, rfl⟩
      obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ (δ / 3 * n) := ⟨_, rfl⟩
      have hE0 : 1 ≤ E := by rw [hE]; exact Real.one_le_rpow one_le_two (by positivity)
      have hLE : (L.length : ℝ) ≤ E := by rw [hE, hL]; exact t1
      -- the width reduction and then D, at each leaf
      have hT : ∀ x ∈ leaves (stepPlain step) (Dd * n) (rootPlain a),
          (Stepped.mapIn leafPlain (Stepped.mapIn widthP D)).Runs x ⌊(A : ℝ) * E⌋₊ (A * (P₁ * M ^ 2) ^ A) (cntN n (leafF x.2)) := fun x hx => by
        rw [hE, hP₁]
        exact leaf_runs hδ' hδB hD hn h1 (t2 x hx).2.1 (t2 x hx).2.2.1 (t2 x hx).2.2.2
      have hS : ∀ i, size ((round (stepPlain step))^[i] ([rootPlain a], [])).1 ≤ P₂ * M ^ 3 := fun i => by
        rw [hP₂]
        exact stack_size hn hm h1 (t4 i).1 (t4 i).2
      have wr := stWalkSum _ _ (stepPlain step) rootPlain (Stepped.mapIn leafPlain (Stepped.mapIn widthP D)) (Dd * n) a
        (fun x hx => (t2 x hx).1) (fun x => cntN n (leafF x.2)) ⌊(A : ℝ) * E⌋₊ (A * (P₁ * M ^ 2) ^ A) (P₂ * M ^ 3) (n + 1) hT hS (by rw [← t3, ← hv]; exact hv2)
      rw [← t3, ← hv, ← hL] at wr
      refine ⟨_, _, Stepped.ite_runs_false (by rw [ha]; simpa using fun h => hnil ((hasNil_iff ψ).1 h)) wr, by omega, ?_⟩
      have hfl : ((⌊(A : ℝ) * E⌋₊ : ℕ) : ℝ) ≤ (A : ℝ) * E := Nat.floor_le (by positivity)
      have hEE : E * E ≤ (2 : ℝ) ^ (δ * n) := by
        rw [hE, ← Real.rpow_add two_pos]
        refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
        have : (0 : ℝ) ≤ δ * n := by positivity
        linarith
      have hE00 : 0 ≤ E := by linarith
      push_cast
      calc (L.length : ℝ) * (((⌊(A : ℝ) * E⌋₊ : ℕ) : ℝ) + 2) ≤ E * ((A : ℝ) * E + 2 * E) := mul_le_mul hLE (by linarith) (by positivity) hE00
        _ = ((A : ℝ) + 2) * (E * E) := by ring
        _ ≤ ((A : ℝ) + 2) * (2 : ℝ) ^ (δ * n) := mul_le_mul_of_nonneg_left hEE (by positivity)
  obtain ⟨T, S, r, hS, hT⟩ := main
  have ro := Stepped.ofFun_runs outW (a, v)
  have hout : outW (a, v) = SatK.binary n v := by rw [ha]; exact outW_eq n ψ v
  rw [hout] at ro
  refine ⟨T + 1 + 1, (Stepped.bind_runs r ro).mono le_rfl (poly_le h1 ?_), ?_⟩
  · have sv : size v ≤ n + 2 := size_nat_le hv2
    have sb := size_binary n v
    have sp : size (a, v) = size a + size v := size_prod _
    have e1 : B₀ * M ^ 3 = P₂ * M ^ 3 + 2 * ((Q + 4) * M ^ 3) + 12 * M ^ 3 := by rw [hB₀]; ring
    have e2 : (Q + 4) * M ^ 2 ≤ (Q + 4) * M ^ 3 := Nat.mul_le_mul_left _ hM23
    rw [sp]
    omega
  · have hc : (A : ℝ) + 4 ≤ ((B₀ + 3 + A * P₁ ^ A + 2 * A : ℕ) : ℝ) := by
      have : A + 4 ≤ B₀ + 3 + A * P₁ ^ A + 2 * A := by omega
      exact_mod_cast this
    calc ((T + 1 + 1 : ℕ) : ℝ) = (T : ℝ) + 2 := by push_cast; ring
      _ ≤ ((A : ℝ) + 2) * (2 : ℝ) ^ (δ * n) + 2 * (2 : ℝ) ^ (δ * n) := by linarith
      _ = ((A : ℝ) + 4) * (2 : ℝ) ^ (δ * n) := by ring
      _ ≤ ((B₀ + 3 + A * P₁ ^ A + 2 * A : ℕ) : ℝ) * (2 : ℝ) ^ (δ * n) := mul_le_mul_of_nonneg_right hc (by positivity)
end SplitCount

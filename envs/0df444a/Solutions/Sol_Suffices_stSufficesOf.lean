-- Prove2me | solution 1 for Suffices.stSufficesOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:13:25.995956+00:00
-- url     : https://prove2.me/submissions/3c1ab025-8d5a-4daa-b18b-546bcda3f40d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Suffices_Loop
import Definitions.Def_Suffices_Total
import Definitions.Def_Exits_Poly
import Definitions.Def_CountKSat_InOut
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Suffices_Main
import Theorems.Thm_CountKSat_stDecU
import Theorems.Thm_Exits_mem_of_mem_tested
import Theorems.Thm_Groundwork_Decode_length_toN
import Theorems.Thm_Groundwork_Decode_mem_toN
import Theorems.Thm_Groundwork_Decode_nil_mem_toN
import Theorems.Thm_Groundwork_Decode_satN_toN
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_const_runs
import Theorems.Thm_Groundwork_Stepped_ite_runs_true
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
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
import Theorems.Thm_Suffices_isKCNF_toN
import Theorems.Thm_Suffices_le_length_enc
import Theorems.Thm_Suffices_length_tested_le
import Theorems.Thm_Suffices_main_bound
import Theorems.Thm_Suffices_satLoop_polyTimeSteps_of
import Theorems.Thm_Suffices_size_input_le
import Theorems.Thm_Suffices_size_sparse_le
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
open Suffices
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Paper SparsificationLemma Enumerate Exits
namespace Suffices
theorem _root_.solution : StSufficesOf := by
  intro HL HT HP δ M τ hδ hM hE
  refine ⟨fun Mc hMc => satLoop_polyTimeSteps_of HP hE Mc hMc, fun Mc A hMc => ?_⟩
  classical
  obtain ⟨c₁, hc₁⟩ := HL (δ / 3) M τ hE
  obtain ⟨c₂, hc₂⟩ := HT δ A (UniformInK.bsumU τ 3) hδ
  obtain ⟨c, hc⟩ : ∃ c, c = c₁ + A * (14 * M + 2) ^ A + 2 * A + c₂ + 22 := ⟨_, rfl⟩
  refine ⟨c, fun n φ h3 => ?_⟩
  obtain ⟨N, hN⟩ : ∃ N, N = (Sat3.enc φ).length + 1 := ⟨_, rfl⟩
  obtain ⟨hn, hm⟩ := le_length_enc φ
  rw [← hN] at hn hm ⊢
  have h1 : 1 ≤ N := by omega
  obtain ⟨hb1, hb2⟩ := main_bound hc h1
  have hE1 : (1 : ℝ) ≤ (2 : ℝ) ^ (δ * n) := Real.one_le_rpow one_le_two (by positivity)
  have hcc : (c₂ : ℝ) ≤ c := by exact_mod_cast (by omega : c₂ ≤ c)
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast (by omega : 1 ≤ c)
  have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
  by_cases hnil : [] ∈ φ
  · -- a formula with an empty clause is unsatisfiable, and is answered at once
    refine ⟨1, false, ?_, ?_, ?_⟩
    · have hdec : decU 3 (Sat3.enc φ) = (List.replicate n (), Decode.toN φ) := stDecU 3 n φ (by norm_num) h3.1
      have hn' : hasNil (Decode.toN φ) = true := by
        rw [hasNil, List.any_eq_true]
        exact ⟨[], (Decode.nil_mem_toN φ).2 hnil, rfl⟩
      have hs : size (List.replicate n (), Decode.toN φ) ≤ 18 * N ^ 2 := size_input_le (by rw [Decode.length_toN]; exact hm)
        (fun D hD => by obtain ⟨⟨C, hC, hl⟩, h⟩ := Decode.mem_toN hD; exact ⟨hl ▸ h3.1 C hC, h⟩) hn h1
      have hN2 : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ h1
      have r := (Stepped.ite_runs_true (p := fun p : List Unit × Fml => hasNil p.2) (N := walkUntil (rule τ) rootC (Stepped.mapIn SparsificationLemma.out (Stepped.mapOut Mc posZ)))
        (a := (List.replicate n (), Decode.toN φ)) hn' (Stepped.const_runs false (List.replicate n (), Decode.toN φ))).mono le_rfl
        (show max (size (List.replicate n (), Decode.toN φ)) (size false) + 1 + 1 ≤ c * N ^ c by rw [size_bool]; omega)
      rw [← hdec] at r
      exact Stepped.mapIn_runs r
    · simp only [Bool.false_eq_true, false_iff]
      rintro ⟨a, ha⟩
      obtain ⟨l, hl, -⟩ := ha [] hnil
      simp at hl
    · push_cast
      nlinarith
  · have hk := isKCNF_toN h3 hnil
    obtain ⟨t, ht⟩ : ∃ t : ℕ, t = ⌈(A : ℝ) * (2 : ℝ) ^ (δ / 3 * n) + A * ((n : ℝ) + 1) ^ A⌉₊ := ⟨_, rfl⟩
    obtain ⟨Sm, hSm⟩ : ∃ Sm, Sm = A * ((14 * M + 2) * N ^ 2) ^ A := ⟨_, rfl⟩
    -- «each with at most M(ε)·n clauses»: the machine for sparse formulas answers on every formula
    -- produced, within t steps
    have hex : ∀ Φ : Formula, ∃ v : ℤ, Φ ∈ produced τ n (Decode.toN φ) → Mc.Runs Φ t Sm v ∧ (0 < v ↔ Φ.Sat) := by
      intro Φ
      by_cases hΦ : Φ ∈ produced τ n (Decode.toN φ)
      · obtain ⟨p1, -, p3⟩ := hE.sparse n _ hk Φ hΦ
        obtain ⟨T, v, r, hv, hT⟩ := hMc n Φ p1 p3
        refine ⟨v, fun _ => ⟨r.mono ?_ ?_, hv⟩⟩
        · have hexp : δ / (3 * M) * Φ.length ≤ δ / 3 * n := by
            have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
            have hl : (Φ.length : ℝ) ≤ M * n := by exact_mod_cast p3
            calc δ / (3 * M) * Φ.length ≤ δ / (3 * M) * (M * n) := mul_le_mul_of_nonneg_left hl (by positivity)
              _ = δ / 3 * n := by field_simp
          have hTt : (T : ℝ) ≤ (t : ℝ) := by
            rw [ht]
            refine (hT.trans ?_).trans (Nat.le_ceil _)
            have h2 := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one_le_two hexp) hA0
            linarith
          exact_mod_cast hTt
        · rw [hSm]
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (size_sparse_le p3 (fun C hC => (p1 C hC).2) hn h1) A)
      · exact ⟨0, fun h => absurd h hΦ⟩
    choose v hv using hex
    have run := hc₁ Mc n φ h3 hnil v t Sm fun Φ hΦ => (hv Φ (mem_of_mem_tested hΦ)).1
    obtain ⟨L, hL⟩ : ∃ L, L = (tested (fun Φ => posZ (v Φ)) (produced τ n (Decode.toN φ))).length := ⟨_, rfl⟩
    rw [← hN, ← hL] at run
    refine ⟨_, _, run.mono le_rfl (by rw [hSm]; exact hb1), ?_, ?_⟩
    · -- φ is satisfiable if and only if at least one of them is (field `sat`)
      have hs := hE.sat n _ hk
      rw [← Decode.satN_toN, List.any_eq_true]
      constructor
      · rintro ⟨Φ, hΦ, hp⟩
        have h0 : 0 < v Φ := by simpa [posZ] using hp
        exact hs.2 ⟨Φ, hΦ, (hv Φ hΦ).2.1 h0⟩
      · intro h
        obtain ⟨Φ, hΦ, hb⟩ := hs.1 h
        exact ⟨Φ, hΦ, by simpa [posZ] using (hv Φ hΦ).2.2 hb⟩
    · -- «at most 2^{δn/3} such formulas … so the total time is O(2^{δn})»
      have hLE : (L : ℝ) ≤ (2 : ℝ) ^ (δ / 3 * n) := by
        rw [hL]
        exact (Nat.cast_le.2 (length_tested_le _ _)).trans (hE.few n _ hk)
      have tot := hc₂ n L (δ / 3 * n) hLE le_rfl
      have htc : (t : ℝ) ≤ (A : ℝ) * (2 : ℝ) ^ (δ / 3 * n) + A * ((n : ℝ) + 1) ^ A + 1 := by
        rw [ht]
        exact (Nat.ceil_lt_add_one (by positivity)).le
      have h2 := mul_le_mul_of_nonneg_left (show (t : ℝ) + 2 ≤ (A : ℝ) * (2 : ℝ) ^ (δ / 3 * n) + A * ((n : ℝ) + 1) ^ A + 3 by linarith) (Nat.cast_nonneg (α := ℝ) L)
      rw [show depth τ n = UniformInK.bsumU τ 3 * n from rfl]
      push_cast
      calc (L : ℝ) * ((t : ℝ) + 2) + (UniformInK.bsumU τ 3 : ℝ) * n + 2
          ≤ (L : ℝ) * ((A : ℝ) * (2 : ℝ) ^ (δ / 3 * n) + A * ((n : ℝ) + 1) ^ A + 3) + (UniformInK.bsumU τ 3 : ℝ) * n + 2 := by linarith
        _ ≤ c₂ * (2 : ℝ) ^ (δ * n) := tot
        _ ≤ c * (2 : ℝ) ^ (δ * n) := mul_le_mul_of_nonneg_right hcc (by positivity)
end Suffices

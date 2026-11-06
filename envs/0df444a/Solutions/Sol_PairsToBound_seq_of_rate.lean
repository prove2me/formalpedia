-- Prove2me | solution 1 for PairsToBound.seq_of_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:47:46.69071+00:00
-- url     : https://prove2.me/submissions/399d31ab-f362-4be1-8f24-d42fef536d8f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_GeneralPieces_Rec_Seq
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Rec_Rate
import Definitions.Def_GeneralPieces_Rec_PartB
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_ClauseBound_Alg_Need
import Definitions.Def_PairsToBound_Pairs
import Theorems.Thm_ClauseBound_Gen_Seq_topK_idx
import Theorems.Thm_ClauseBound_Gen_Seq_two_le_K
import Theorems.Thm_GeneralPieces_DefGenPieces_logb_nonneg
import Theorems.Thm_GeneralPieces_PartAUse_e_le_one
import Theorems.Thm_GeneralPieces_PartAUse_inv_logK_pow_le_e
import Theorems.Thm_GeneralPieces_PartAUse_two_le_K
import Theorems.Thm_GeneralPieces_PartA_thmRunningTime_a
import Theorems.Thm_GeneralPieces_Trim_length_bitsOf
import Theorems.Thm_GeneralPieces_Trim_length_rep
import Theorems.Thm_GeneralPieces_thmRunningTime_a
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
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
import Theorems.Thm_PaddedDescent_F_Top_correct
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] GeneralPieces.Trim.length_bitsOf
attribute [local simp] GeneralPieces.Trim.length_rep
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
open PairsToBound
open Turing Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Seq Levels.Gen GeneralPieces MainTheoremForms
namespace PairsToBound
theorem _root_.solution (hCh : StChain2) (hR : StRate2) (hSolve : ∀ P, StSolveG2 P) (hNeed : ∀ P, StNeedG P) (c : ℕ) :
    ∃ C₀ : ℕ, ∀ (P : PiecesF) (ρ : ℝ) (x₀ : ℕ), 1 / 2 ≤ ρ → ρ < 1 → Par P ρ c → P.m = 1 → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ →
      ∀ pick : U → U × (List Step × U), PolyT pick → (∀ b, (pick b).2 = idx P x₀ (pick b).1.length) → (∀ b, K x₀ 0 ≤ b.length → K x₀ (pick b).1.length ≤ b.length) →
        (∀ b, b.length < K x₀ ((pick b).1.length + 1)) →
        ∃ Q : (solverOf P).Seq (e ρ x₀) C₀, (∀ l, Q.idx l = idx P x₀ l) ∧ Q.pick = pick := by
  obtain ⟨C, hC'⟩ := hR c
  refine ⟨C + 10, fun P ρ x₀ hρ hρ1 hP hm hx hx2 pick hp1 hp2 hp3 hp4 => ?_⟩
  have hC := hC' P ρ x₀ hρ hρ1 hP hm hx hx2
  have hK : ∀ l, (solverOf P).K (idx P x₀ l) = K x₀ l := topK_idx P x₀
  have hA := PartA.thmRunningTime_a ρ x₀ hρ hρ1 hx
  refine ⟨{
    idx := idx P x₀
    K_two := fun l => by rw [hK]; exact two_le_K x₀ l hx
    K_lt := fun l => by rw [hK, hK]; exact (hA.K_lt_le l).1
    K_le := fun l => by
      rw [hK, hK]
      exact (hA.K_lt_le l).2.trans (Nat.pow_le_pow_right (by have := two_le_K x₀ l hx; omega) (by omega))
    e_le := fun l => PartAUse.e_le_one hA (by linarith) hρ1.le l
    e_ge := fun l => by rw [hK]; exact PartAUse.inv_logK_pow_le_e hA hρ (by omega) l (C + 10) (by omega)
    correct := ?_
    rate := ?_
    pick := pick
    pick_poly := hp1
    pick_idx := hp2
    pick_le := fun b hb => by
      rw [hK] at hb
      rw [hp2, hK]
      exact hp3 b hb
    pick_max := fun b => by rw [hK]; exact hp4 b }, fun _ => rfl, rfl⟩
  · rintro pad i lam B I ⟨l, rfl⟩ hlam hI hpad
    rw [hK] at hI ⊢
    have h1 : 2 ^ needG P (K x₀ l) lam B 1 1 (sched P x₀ l) ≤ pad.length := by
      rw [← topK_idx P x₀ l]
      simpa [solverOf, idx] using hpad
    have h2 := hSolve P pad (K x₀ 0) (sched P x₀ l) (K x₀ l) lam B I (hCh P ρ c x₀ hP hm hx hx2 l lam hlam)
      (hNeed P pad.length (K x₀ l) lam B 1 1 (sched P x₀ l) h1) hI
    simpa [solverOf, idx, rep] using h2
  · intro l lam B hlam hB
    rw [hK]
    have h1 : (solverOf P).need (idx P x₀ l, List.replicate lam (), List.replicate B ()) = needG P (K x₀ l) lam B 1 1 (sched P x₀ l) := by
      rw [← topK_idx P x₀ l]
      simp [solverOf, idx]
    rw [h1]
    refine (hC l lam B hlam hB).trans ?_
    have h2 : (1 : ℝ) ≤ (K x₀ l : ℝ) * ((lam : ℝ) + B) := by
      have a : (1 : ℝ) ≤ (K x₀ l : ℝ) := by have := two_le_K x₀ l hx; exact_mod_cast (by omega : 1 ≤ K x₀ l)
      have b : (1 : ℝ) ≤ (lam : ℝ) := by exact_mod_cast hlam
      have d : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg _
      nlinarith
    have h3 : 0 ≤ Real.logb 2 ((K x₀ l : ℝ) * ((lam : ℝ) + B)) := Real.logb_nonneg (by norm_num) h2
    have h4 : (C : ℝ) * (K x₀ l : ℝ) ^ 2 * Real.logb 2 ((K x₀ l : ℝ) * ((lam : ℝ) + B)) ≤
        ((C + 10 : ℕ) : ℝ) * (K x₀ l : ℝ) ^ 2 * Real.logb 2 ((K x₀ l : ℝ) * ((lam : ℝ) + B)) := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity)) h3
      push_cast; linarith
    linarith
end PairsToBound

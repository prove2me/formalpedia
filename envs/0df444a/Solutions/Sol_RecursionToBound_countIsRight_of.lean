-- Prove2me | solution 1 for RecursionToBound.countIsRight_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:03:58.4105+00:00
-- url     : https://prove2.me/submissions/6aeac8c5-fefb-44ee-afa0-48eaf7d0c5c4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_RecursionToBound_Tree
import Definitions.Def_PairsToBound_Width
import Definitions.Def_PairsToBound_Exhaust
import Definitions.Def_SparsificationLemma_StepSparsify
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_SparsificationLemma_Len
import Definitions.Def_SparsificationLemma_Cal_Facts
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_SparsificationLemma_Cal_Thr
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_StepSparsify_Walk
import Definitions.Def_UniformInK_Tree_Stack
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSatRate_Walk
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_RecursionWithPieces_Main
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_WidthK_Decode
import Definitions.Def_ToTuring_Poly_NetFun
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Definitions.Def_RecursionToBound_Correct
import Theorems.Thm_RecursionToBound_Correct_countAll_eq
import Theorems.Thm_ClauseBound_Alg_Decode_stDecM
import Theorems.Thm_CountKSatRate_stBruteC
import Theorems.Thm_CountKSat_stDecU
import Theorems.Thm_GeneralPieces_Series_cf_add
import Theorems.Thm_GeneralPieces_Series_cf_neg
import Theorems.Thm_GeneralPieces_Series_cf_smul
import Theorems.Thm_GeneralPieces_Series_cf_sub
import Theorems.Thm_GeneralPieces_Series_cf_zero
import Theorems.Thm_GeneralPieces_Trim_length_bitsOf
import Theorems.Thm_GeneralPieces_Trim_length_rep
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_count
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
import Theorems.Thm_P2M_VariableBound_VariablesA_one_le_C__74197dd70aad
import Theorems.Thm_PaddedDescent_F_CertNet_nU
import Theorems.Thm_PairsToBound_outW_replicate
import Theorems.Thm_PairsToBound_widthOr3Stmt
import Theorems.Thm_RecursionToBound_Eps_pos_of_le
import Theorems.Thm_RecursionToBound_widthOnTheCode
import Theorems.Thm_VariableBound_VariablesA_e_ge_n
import Theorems.Thm_VariableBound_VariablesA_e_pos
import Theorems.Thm_VariableBound_VariablesA_isLevel_pick
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] PaddedDescent.F.CertNet.nU
attribute [local simp] GeneralPieces.Series.cf_add
attribute [local simp] GeneralPieces.Series.cf_neg
attribute [local simp] GeneralPieces.Series.cf_smul
attribute [local simp] GeneralPieces.Series.cf_sub
attribute [local simp] GeneralPieces.Series.cf_zero
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
open RecursionToBound
open Finset Turing Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound
open PaddedDescent.F.Mark (occ)
open Sat3 (CNF)
open PaddedDescent.F.Mark (WfL nSat)
open Groundwork.Sparsify (PFml leaves round)
namespace RecursionToBound
theorem _root_.solution (hSet : OutputsAreWithinTheSetting) (hCut : CutOffIsIdle) (hPlan : PlanFailsOnlyAboveN) : CountIsRight := by
  intro Idx _ S e C₀ Q hS num hnum
  obtain ⟨n₀, hn₀⟩ := hSet C₀ (VariableBound.VariablesA.one_le_C₀ Q)
  refine ⟨n₀, fun n₁ hn₁ k n φ hK hk hk4 hφ pad hpad => ?_⟩
  have hk1 : 1 ≤ k := by omega
  obtain ⟨-, hdec⟩ := Decode.stDecM k n φ hk1 hφ.1
  have hn : nU (SatM.enc k φ) = n := by rw [nU, hdec, List.length_replicate]
  obtain ⟨l, hl⟩ : ∃ l, IsLevel S Q n l := ⟨_, VariableBound.VariablesA.isLevel_pick Q hK⟩
  obtain ⟨hw3, hwk, hwle⟩ := widthOr3Stmt n φ
  obtain ⟨k', hk'⟩ : ∃ k', k' = widthOr3 φ := ⟨_, rfl⟩
  rw [← hk'] at hw3 hwk hwle
  have hwU : widthU (SatM.enc k φ) = k' := (widthOnTheCode.1 k n φ hk1 hφ).trans hk'.symm
  obtain ⟨hnumU, hidx⟩ := widthOnTheCode.2 Idx S e C₀ Q num k n l φ hk1 hφ hl
  obtain ⟨r, hr⟩ : ∃ r, r = num (List.replicate l (), List.replicate (S.K (Q.idx l)) ()) := ⟨_, rfl⟩
  rw [← hr] at hnumU
  have hk'k : k' ≤ k := (hwle k hk1 hφ).1.trans (max_le le_rfl hk)
  have hk'4 : (k' : ℝ) ^ 4 ≤ MainTheoremForms.lg n := (pow_le_pow_left₀ (Nat.cast_nonneg k') (by exact_mod_cast hk'k) 4).trans hk4
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_pow _ _ (by have := Q.K_two 0; omega)) hK
  have hcut : kcU k' n = k' := hCut k' n hn1 hk'4
  have hplan : plan S n₁ Q.pick num (SatM.enc k φ) = planAt S n₁ k' n (Q.idx l) r := by rw [plan, hwU, hn, hcut, hidx, hnumU]
  have hnumber : (bif (plan S n₁ Q.pick num (SatM.enc k φ)).isNone then bruteU (SatM.enc k φ, pad)
      else countAll S (kcU (widthU (SatM.enc k φ)) (nU (SatM.enc k φ))) (numU S Q.pick num (SatM.enc k φ)) (idxU Q.pick (SatM.enc k φ)) (fmlOf (SatM.enc k φ)) pad) = SatK.numSat φ := by
    rw [expo, hplan, hn] at hpad
    rw [hplan, hwU, hn, hcut, hidx, hnumU, hdec]
    cases hpl : planAt S n₁ k' n (Q.idx l) r with
    | none =>
      rw [hpl, Option.getD_none] at hpad
      have hb := stBruteC k n φ hk1 hφ pad hpad
      rw [bruteN, nK, stDecU k n φ hk1 hφ.1] at hb
      simp only [List.length_replicate] at hb
      simp only [Option.isNone_none, cond_true, bruteU, hdec, List.length_replicate]
      exact hb
    | some v =>
      rw [hpl, Option.getD_some] at hpad
      obtain ⟨c1, c2, -⟩ := (hPlan Idx S hS n₁ k' n (Q.idx l) r).1 v hpl
      rw [c2] at hpad
      obtain ⟨hlo, hhi⟩ := hnum.2 l
      rw [← hr] at hlo hhi
      obtain ⟨hr1, hr2⟩ := Eps.pos_of_le (VariableBound.VariablesA.e_pos Q l) hlo
      simp only [Option.isNone_some, cond_false]
      refine Correct.countAll_eq Q φ pad hw3 (hwk hφ.2) hr1 hr2 (fun Δ h2 hb => ?_) hpad
      obtain ⟨-, -, -, d1, d2⟩ := hn₀ k' n Δ r (e l) (hn₁.trans c1) hw3 hk'4 (VariableBound.VariablesA.e_ge_n Q hl) (Q.e_le l) hlo hhi h2 hb
      exact ⟨d1, d2⟩
  unfold count
  dsimp only
  rw [hnumber, hdec]
  exact outW_replicate _ _ _
end RecursionToBound

-- Prove2me | solution 1 for RecursionToBound.Correct.countAll_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:51:34.15236+00:00
-- url     : https://prove2.me/submissions/afd2170e-8d9d-440f-85e3-4b68e89eda4d

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
import Theorems.Thm_RecursionToBound_Correct_depth_le
import Theorems.Thm_RecursionToBound_Correct_walk_eq
import Theorems.Thm_RecursionToBound_Correct_countOutput_eq
import Theorems.Thm_RecursionToBound_Correct_numSat_le
import Theorems.Thm_RecursionToBound_Correct_numSat_of_nil
import Theorems.Thm_RecursionToBound_Correct_length_le_inLen
import Theorems.Thm_CountKSat_CountTop_numSat_le
import Theorems.Thm_CountKSat_CountTop_numSat_of_nil
import Theorems.Thm_CountKSat_stCntToN
import Theorems.Thm_GeneralPieces_Pcs_Le_sum
import Theorems.Thm_GeneralPieces_Ring_mem_toN
import Theorems.Thm_GeneralPieces_Series_cf_add
import Theorems.Thm_GeneralPieces_Series_cf_neg
import Theorems.Thm_GeneralPieces_Series_cf_smul
import Theorems.Thm_GeneralPieces_Series_cf_sub
import Theorems.Thm_GeneralPieces_Series_cf_zero
import Theorems.Thm_GeneralPieces_Trim_length_bitsOf
import Theorems.Thm_GeneralPieces_Trim_length_rep
import Theorems.Thm_Groundwork_Decode_length_toN
import Theorems.Thm_Groundwork_Decode_mem_toN
import Theorems.Thm_Groundwork_Decode_nil_mem_toN
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
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
import Theorems.Thm_RecursionToBound_Eps_le_one
import Theorems.Thm_RecursionToBound_Eps_one_le_alpha
import Theorems.Thm_RecursionToBound_Eps_pos
import Theorems.Thm_RecursionToBound_ownDeltaIsBounded
import Theorems.Thm_RecursionToBound_walkTreeIsSparsify
import Theorems.Thm_SparsificationLemma_Cal_sparsABC
import Theorems.Thm_SparsificationLemma_Cal_stAlpha
import Theorems.Thm_SparsificationLemma_StepSparsify_count_eq_sum
import Theorems.Thm_SparsificationLemma_StepSparsify_one_le_alpha
import Theorems.Thm_SparsificationLemma_StepSparsify_outputs_le
import Theorems.Thm_SparsificationLemma_StepSparsify_sparsABC
import Theorems.Thm_SparsificationLemma_stNoTaut
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum
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
open RecursionToBound.Correct
namespace RecursionToBound.Correct
theorem _root_.solution {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀) {k n l : ℕ} {r : ℕ × ℕ} (φ : CNF n) (pad : U) (hk : 3 ≤ k) (hφ : SatK.IsKCNF k φ)
    (hr1 : 0 < r.1) (hr2 : 0 < r.2) (hΔ : ∀ Δ : ℕ, 2 ≤ Δ → Δ ≤ occBound k r → Δ ≤ n + 1 ∧ 29 * LD Δ + 19 ≤ n)
    (hpad : 2 ^ (needOutputs S k r (Q.idx l) n + needWalk k r n) ≤ pad.length) :
    countAll S k r (Q.idx l) (List.replicate n (), Decode.toN φ) pad = SatK.numSat φ := by
  unfold countAll
  dsimp only
  rw [List.length_replicate]
  have hnilψ : hasNil (Decode.toN φ) = true ↔ [] ∈ φ := by
    rw [← Decode.nil_mem_toN]
    simp [hasNil, List.any_eq_true]
  by_cases hnil : [] ∈ φ
  · rw [hnilψ.2 hnil, cond_true, numSat_of_nil hnil]
  · have hn' : hasNil (Decode.toN φ) = false := by
      rw [← Bool.not_eq_true]
      exact fun h => hnil (hnilψ.1 h)
    rw [hn', cond_false]
    have h0 := Eps.pos hr1 hr2
    have h1 := Eps.le_one r
    obtain ⟨-, -, hα, -, -⟩ := Cal.stAlpha k (epsOf r) hk h0 h1
    have hψ0 : IsKCNF k n (Decode.toN φ) := by
      intro D hD'
      obtain ⟨⟨C, hC, hl⟩, h⟩ := Decode.mem_toN hD'
      refine ⟨?_, hl ▸ hφ.1 C hC, h⟩
      rintro rfl
      exact hnil ((Decode.nil_mem_toN φ).1 hD')
    have hψ : IsKCNF k n (noTaut (Decode.toN φ)) := (stNoTaut _).2.1 k n hψ0
    have hm : (noTaut (Decode.toN φ)).length ≤ inLen k n :=
      (List.length_filter_le _ _).trans (by rw [Decode.length_toN]; exact length_le_inLen (by omega) hφ)
    have hpa : 2 ^ needOutputs S k r (Q.idx l) n ≤ pad.length := (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)).trans hpad
    have hpw : ∀ a : ℕ, a ≤ needWalk k r n → 2 ^ a ≤ pad.length := fun a ha =>
      (Nat.pow_le_pow_right (by norm_num) (ha.trans (Nat.le_add_left _ _))).trans hpad
    have hout := walkTreeIsSparsify k n (bsumU (32 * Cal.alphaC k (epsOf r)) k * n) r (Decode.toN φ) hk hr1 hr2 hψ0
      (depth_le (Eps.one_le_alpha hk hr1 hr2) (by omega) n)
    unfold thresholds at hout ⊢
    obtain ⟨L, hL⟩ : ∃ L, L = leaves (stepC (Cal.thetaC (Cal.alphaC k (epsOf r))) k) (bsumU (32 * Cal.alphaC k (epsOf r)) k * n) (rootC (List.replicate n (), noTaut (Decode.toN φ))) := ⟨_, rfl⟩
    rw [← hL] at hout
    have hval : ∀ x ∈ L, countOutput S k pad (Q.idx l) n x = cntN n (out x) := by
      intro x hx
      have hmem : out x ∈ Cal.sparsify k n (epsOf r) (Decode.toN φ) := by
        rw [← hout]
        exact List.mem_map.2 ⟨x, hx, rfl⟩
      have hb := ownDeltaIsBounded k n r (Decode.toN φ) hk hr1 hr2 hψ0 (out x) hmem
      obtain ⟨c1, c2⟩ := hΔ (SparsificationLemma.StepSparsify.DeltaOf n (out x)) (le_max_left _ _) hb
      exact countOutput_eq Q pad x ((SparsificationLemma.StepSparsify.sparsABC k n (epsOf r) (Decode.toN φ) hk h0 h1 hψ0).1 _ hmem).1 hb c1 c2 hpa
    have hsum : (L.map (countOutput S k pad (Q.idx l) n)).sum = SatK.numSat φ := by
      calc (L.map (countOutput S k pad (Q.idx l) n)).sum = (L.map fun x => cntN n (out x)).sum := by rw [List.map_congr_left hval]
        _ = ((L.map out).map (cntN n)).sum := by simp only [List.map_map, Function.comp_def]
        _ = cntN n (Decode.toN φ) := by
          rw [hout]
          exact (SparsificationLemma.StepSparsify.count_eq_sum hk h0 h1 hψ0).symm
        _ = _ := stCntToN n φ
    have hlen : L.length ≤ 2 ^ ⌈epsOf r * (n : ℚ)⌉₊ := by
      have a1 := SparsificationLemma.StepSparsify.outputs_le hk h0 h1 hψ0
      rw [← hout, List.length_map] at a1
      have a2 : ((epsOf r : ℚ) : ℝ) * (n : ℝ) ≤ ((⌈epsOf r * (n : ℚ)⌉₊ : ℕ) : ℝ) := by exact_mod_cast Nat.le_ceil (epsOf r * (n : ℚ))
      have a3 : (L.length : ℝ) ≤ ((2 ^ ⌈epsOf r * (n : ℚ)⌉₊ : ℕ) : ℝ) := by
        calc (L.length : ℝ) ≤ (2 : ℝ) ^ (((epsOf r : ℚ) : ℝ) * (n : ℝ)) := a1
          _ ≤ (2 : ℝ) ^ ((⌈epsOf r * (n : ℚ)⌉₊ : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two a2
          _ = _ := by rw [Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
      exact_mod_cast a3
    have hrounds : 2 * L.length ≤ pad.length + 1 := by
      have b1 := hpw (⌈epsOf r * (n : ℚ)⌉₊ + 2) (by unfold needWalk; omega)
      rw [pow_add] at b1
      omega
    have hstack : stackLenCU k (32 * Cal.alphaC k (epsOf r)) n (inLen k n) ≤ pad.length :=
      (Nat.lt_size_self _).le.trans (hpw _ (by unfold needWalk; omega))
    have hlt : (L.map (countOutput S k pad (Q.idx l) n)).sum < 2 ^ (n + 1) := by
      rw [hsum]
      exact (numSat_le φ).trans_lt (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self n))
    rw [hL] at hrounds hlt hsum
    rw [walk_eq (by omega) hα hψ hm pad _ hrounds hstack hlt, hsum]
end RecursionToBound.Correct

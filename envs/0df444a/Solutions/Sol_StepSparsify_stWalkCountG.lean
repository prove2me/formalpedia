-- Prove2me | solution 1 for StepSparsify.stWalkCountG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:56:52.489202+00:00
-- url     : https://prove2.me/submissions/855f84ba-bae1-4932-afa5-c7e38dbfba1b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_StepSparsify_Walk
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_UniformInK_Tree_Stack
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSatRate_Top
import Definitions.Def_CountKSatRate_Top
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_StepSparsify_WalkCount
import Theorems.Thm_StepSparsify_cntN_noTaut
import Theorems.Thm_StepSparsify_length_noTaut_le
import Theorems.Thm_CountKSatRate_Top_iterate_le_sum
import Theorems.Thm_CountKSatRate_stRoundS
import Theorems.Thm_CountKSatRate_stRoundSEnd
import Theorems.Thm_CountKSat_CountTop_numSat_le
import Theorems.Thm_CountKSat_CountTop_numSat_of_nil
import Theorems.Thm_CountKSat_stCntToN
import Theorems.Thm_Groundwork_DecodeK_length_enc
import Theorems.Thm_Groundwork_DecodeK_length_enc_succ_le
import Theorems.Thm_Groundwork_Decode_length_enc
import Theorems.Thm_Groundwork_Decode_length_enc_succ_le
import Theorems.Thm_Groundwork_Decode_length_toN
import Theorems.Thm_Groundwork_Decode_mem_toN
import Theorems.Thm_Groundwork_Decode_nil_mem_toN
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_Prog_SatTopK_length_enc
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
import Theorems.Thm_SparsificationLemma_stNoTaut
import Theorems.Thm_StepSparsify_stWalkSG
import Theorems.Thm_UniformInK_stStateLenU
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum
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
open StepSparsify
open Finset Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Top ClauseBound.TopN UniformInK SparsificationLemma
open Groundwork.Sparsify (PFml leaves round)
namespace StepSparsify
theorem _root_.solution : StWalkCountG := by
  intro Θ Lc hS k s n φ pad val hk h3 hs a3 a4 hvalx
  have hnilψ : hasNil (Decode.toN φ) = true ↔ [] ∈ φ := by
    rw [← Decode.nil_mem_toN]
    simp [hasNil, List.any_eq_true]
  by_cases hnil : [] ∈ φ
  · rw [hnilψ.2 hnil, cond_true, CountTop.numSat_of_nil hnil]
  · have hn' : hasNil (Decode.toN φ) = false := by
      rw [← Bool.not_eq_true]; exact fun h => hnil (hnilψ.1 h)
    rw [hn', cond_false]
    have hm : φ.length ≤ inLen k n := by
      have h := DecodeK.length_enc k φ
      have h' := DecodeK.length_enc_succ_le (φ := φ) h3
      have hB : 0 < k * (Nat.log2 (2 * n) + 1) := Nat.mul_pos hk (Nat.succ_pos _)
      have := Nat.le_mul_of_pos_right φ.length hB
      unfold inLen
      omega
    obtain ⟨m, hmdef⟩ : ∃ m, m = inLen k n := ⟨_, rfl⟩
    rw [← hmdef] at hm a4
    have hψ0 : IsKCNF k n (Decode.toN φ) := by
      intro D hD'
      obtain ⟨⟨C, hC, hl⟩, h⟩ := Decode.mem_toN hD'
      refine ⟨?_, hl ▸ h3.1 C hC, h⟩
      rintro rfl
      exact hnil ((Decode.nil_mem_toN φ).1 hD')
    have hcnt : cntN n (noTaut (Decode.toN φ)) = SatK.numSat φ := by rw [cntN_noTaut, stCntToN n φ]
    have hψl0 : (noTaut (Decode.toN φ)).length ≤ m := (length_noTaut_le _).trans (by rw [Decode.length_toN]; exact hm)
    have hψne0 : IsKCNF k n (noTaut (Decode.toN φ)) := (stNoTaut _).2.1 k n hψ0
    have hψnt0 : ∀ C ∈ noTaut (Decode.toN φ), ∀ l ∈ C, (l.1, !l.2) ∉ C := (stNoTaut _).2.2
    obtain ⟨ψ, hψ⟩ : ∃ ψ : PFml, ψ = noTaut (Decode.toN φ) := ⟨_, rfl⟩
    rw [← hψ] at hcnt hψl0 hψne0 hψnt0 ⊢
    obtain ⟨t1, t2, t3, t4⟩ := hS.tree k n s hk hs ψ hψne0 hψnt0
    obtain ⟨θ, hθ⟩ : ∃ θ, θ = Θ k s := ⟨_, rfl⟩
    obtain ⟨τ, hτ⟩ : ∃ τ, τ = tauOf s := ⟨_, rfl⟩
    rw [← hθ, ← hτ] at t1 t2 t3 t4
    rw [← hθ]
    rw [← hτ] at a4
    obtain ⟨r, hr⟩ : ∃ r, r = rootC (List.replicate n (), ψ) := ⟨_, rfl⟩
    rw [← hr] at t1 t2 t3 t4 ⊢
    obtain ⟨L, hL⟩ : ∃ L, L = leaves (stepC θ k) (bsumU τ k * n) r := ⟨_, rfl⟩
    have hleaf : ∀ x ∈ leaves (stepC θ k) (bsumU τ k * n) r, stepC θ k x = none := fun x hx => (t2 x hx).1
    have hval : ∀ x ∈ L, val x = cntN n (leafF x) := by
      intro x hx
      obtain ⟨-, hxl, hx1, ho, hs'⟩ := t2 x (hL ▸ hx)
      exact hvalx x hxl hx1 ho hs'
    have hsum : (L.map val).sum = SatK.numSat φ := by
      rw [List.map_congr_left hval, ← hcnt, t3, hL]
    rw [← hL] at t1
    rw [stWalkSG θ k pad val r (bsumU τ k * n) hleaf (by rw [← hL]; omega) fun i => ?_, ← hL, hsum]
    refine le_trans ?_ a4
    obtain ⟨s1, s2⟩ := t4 i
    have hc : ((roundS (stepC θ k) val)^[i] ([r], 0)).2 < 2 ^ (n + 1) := by
      have h1 := iterate_le_sum stRoundSEnd (stepC θ k) val (bsumU τ k * n) r hleaf i
      rw [← hL, hsum] at h1
      have h2 := CountTop.numSat_le φ
      have h4 : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have e := stRoundS _ (stepC θ k) val i [r] []
    rw [List.map_nil, List.sum_nil] at e
    rw [e] at hc ⊢
    exact stStateLenU k τ n m _ _ s1 (fun x hx => ⟨(s2 x hx).1.trans (Nat.mul_le_mul_right _ hψl0), (s2 x hx).2⟩) hc
end StepSparsify

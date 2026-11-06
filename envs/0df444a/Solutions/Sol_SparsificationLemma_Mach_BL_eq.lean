-- Prove2me | solution 1 for SparsificationLemma.Mach.BL_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:08:23.194011+00:00
-- url     : https://prove2.me/submissions/17cdc2d9-98b9-432e-b5b5-4d9244de1f5f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Walk
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_UniformInK_Tree_Tree
import Definitions.Def_UniformInK_Spars_Main
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSatRate_Leaf
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Definitions.Def_SparsificationLemma_Mach_Len
import Theorems.Thm_SparsificationLemma_Mach_map_walkL
import Theorems.Thm_SparsificationLemma_Mach_codeP_eq
import Theorems.Thm_SparsificationLemma_Mach_dec_encIn
import Theorems.Thm_SparsificationLemma_Mach_length_encIn
import Theorems.Thm_SparsificationLemma_Mach_eL_encIn
import Theorems.Thm_SparsificationLemma_Mach_isKCNF_toN
import Theorems.Thm_SparsificationLemma_Mach_pad_enough
import Theorems.Thm_Groundwork_Decode_length_toN
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
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
import Theorems.Thm_UniformInK_stLeavesU
import Theorems.Thm_UniformInK_stParU
attribute [local fun_prop] Groundwork.PolyT.all
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
open SparsificationLemma SparsificationLemma.Mach
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent PaddedDescent.F ClauseBound.Alg SparsificationLemma.Geo
namespace SparsificationLemma.Mach
theorem _root_.solution (k n s : ℕ) (φ : Sat3.CNF n) (hk : 1 ≤ k) (hs : s0U k ≤ s) (hφ : SatK.IsKCNF k φ) (hnil : [] ∉ φ) :
    BL (encIn s k φ, PaddedDescent.pad (eL (encIn s k φ))) = code (outTau k n (tauOf s) (Decode.toN φ)) := by
  obtain ⟨d1, d2, d3⟩ := dec_encIn s k n φ hk hφ.1
  have he := eL_encIn s k n φ hk hφ.1
  have hN := length_encIn s k φ
  obtain ⟨N, hNdef⟩ : ∃ N, N = (encIn s k φ).length := ⟨_, rfl⟩
  rw [← hNdef] at he hN
  have hm : φ.length ≤ φ.length * (k * (Nat.log2 (2 * n) + 1)) := Nat.le_mul_of_pos_right _ (Nat.mul_pos hk (Nat.succ_pos _))
  obtain ⟨hτ1, hτ2⟩ := (stParU k s hk).2 hs
  obtain ⟨e, hedef⟩ : ∃ e, e = eL (encIn s k φ) := ⟨_, rfl⟩
  rw [← hedef] at he ⊢
  have hlen : (PaddedDescent.pad e).length = 2 ^ e := List.length_replicate
  have hp2 := pad_enough (n / 2 ^ s) (k := k) (n := n) (m := (Decode.toN φ).length) (N := N) (by omega) (by omega) (by rw [Decode.length_toN]; omega)
  rw [← he, ← hlen] at hp2
  have hp1 : 2 * 2 ^ (n / 2 ^ s + 1) ≤ (PaddedDescent.pad e).length + 1 := by
    have : 2 ^ (n / 2 ^ s + 1) * 2 ≤ 2 ^ (n / 2 ^ s + 1) * (nodeLen k n (Decode.toN φ).length + 2) := Nat.mul_le_mul_left _ (by omega)
    omega
  obtain ⟨w1, w2⟩ := map_walkL hk hτ1 hτ2 (isKCNF_toN hφ.1 hnil) (stLeavesU k n s hk hs) hp1 hp2
  have hke : k ≤ e ∧ Nat.size N ≤ e := by
    generalize n / 2 ^ s = a at he
    omega
  have hmin : min k (Nat.log 2 (PaddedDescent.pad e).length) = k := by
    rw [hlen, Nat.log_pow (by norm_num)]
    exact min_eq_left hke.1
  have hn : n ≤ (PaddedDescent.pad e).length := by
    have h1 : N < 2 ^ Nat.size N := Nat.lt_size_self N
    have h2 : 2 ^ Nat.size N ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) hke.2
    omega
  simp only [BL, d1, d2, d3, hmin]
  rw [w1, codeP_eq fun Φ hΦ C hC l hl => ((w2 Φ hΦ C hC l hl).le).trans hn]
end SparsificationLemma.Mach

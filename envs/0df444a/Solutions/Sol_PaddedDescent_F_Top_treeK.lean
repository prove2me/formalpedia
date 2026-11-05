-- Prove2me | solution 1 for PaddedDescent.F.Top.treeK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:45:45.598202+00:00
-- url     : https://prove2.me/submissions/34cb43ff-a4c7-428e-805c-440cb6dd536f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_NSat
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_PaddedDescent_F_Top
import Theorems.Thm_PaddedDescent_F_Top_len_list_le
import Theorems.Thm_PaddedDescent_F_Top_len_fml_le
import Theorems.Thm_PaddedDescent_F_Top_prog
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Sparsify_roundB_iterate
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
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.length
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
open PaddedDescent PaddedDescent.F PaddedDescent.F.Top
open Finset Groundwork Groundwork.Prog
open Groundwork.Sparsify (PFml leaves rootP roundB round)
open WidthK (theta bsum leafC)
open WidthK.Prog (stepK)
open PaddedDescent.F.Mark (WfL occ nSat)
namespace PaddedDescent.F.Top
theorem _root_.solution (hLf : StLeaf) {k τ n m : ℕ} (hτ : 1 ≤ τ) (ψ : Fml) (hψl : ψ.length ≤ m)
    (hψne : ∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) (test : PFml → Bool)
    (htest : ∀ x : Fml, x.length ≤ (leafC τ k + 2) * n → WfL k n [x] → (∀ v, (occ x v).length ≤ leafC τ k + 2) →
      (test x = true ↔ Fml.Sat x)) :
    (∀ x ∈ leaves (stepK (theta τ) k) (bsum τ k * n) (rootP ψ), stepK (theta τ) k x = none) ∧
    (leaves (stepK (theta τ) k) (bsum τ k * n) (rootP ψ)).length ≤ ∑ j ∈ range (k * n / τ + 1), (bsum τ k * n).choose j ∧
    (∀ i, len ((roundB (stepK (theta τ) k) test)^[i] ([rootP ψ], false)) ≤ stackLen k τ n m) ∧
    ((leaves (stepK (theta τ) k) (bsum τ k * n) (rootP ψ)).any test = true ↔ Fml.Sat ψ) := by
  obtain ⟨t1, t2, t3, t4⟩ := prog τ k n hτ ψ hψne
  obtain ⟨L, hL⟩ : ∃ L, L = leaves (stepK (theta τ) k) (bsum τ k * n) (rootP ψ) := ⟨_, rfl⟩
  rw [← hL] at t1 t2 t3 ⊢
  have hleaf : ∀ x ∈ L, (test x = true ↔ Fml.Sat x) := fun x hx => by
    obtain ⟨l1, l2⟩ := hLf k τ n ψ hτ hψne x (hL ▸ hx)
    refine htest x ((t2 x hx).2.1.trans (Nat.mul_le_mul_right n (by omega))) ?_ fun v => (l2 v).trans (by omega)
    intro y hy C hC
    rw [List.mem_singleton.1 hy] at hC
    exact ⟨l1 C hC, (t2 x hx).2.2 C hC⟩
  refine ⟨fun x hx => (t2 x hx).1, t1, fun i => ?_, ?_⟩
  · obtain ⟨s1, s2⟩ := t4 i
    have e := Sparsify.roundB_iterate (stepK (theta τ) k) test i [rootP ψ] []
    rw [List.any_nil] at e
    rw [e, len_pair, len_bool, stackLen]
    have hf : ∀ x ∈ ((round (stepK (theta τ) k))^[i] ([rootP ψ], [])).1, len x ≤ 2 ^ k * m * (k * (3 * n + 5) + 10) + 2 := fun x hx =>
      len_fml_le ((s2 x hx).1.trans (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hψl)) (s2 x hx).2
    have h := len_list_le s1 hf
    have e4 : 2 ^ k * m * (k * (3 * n + 5) + 10) + 2 + 2 = 2 ^ k * m * (k * (3 * n + 5) + 10) + 4 := rfl
    rw [e4] at h
    omega
  · simp only [List.any_eq_true]
    constructor
    · rintro ⟨x, hx, hx'⟩
      obtain ⟨a, ha⟩ := (hleaf x hx).1 hx'
      exact ⟨a, (t3 fun l => a l.1 = l.2).2 ⟨x, hx, ha⟩⟩
    · rintro ⟨a, ha⟩
      obtain ⟨x, hx, h⟩ := (t3 fun l => a l.1 = l.2).1 ha
      exact ⟨x, hx, (hleaf x hx).2 ⟨a, h⟩⟩
end PaddedDescent.F.Top

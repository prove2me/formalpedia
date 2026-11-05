-- Prove2me | solution 1 for WidthK.ProgMain.sparsify_prog_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:04:56.943211+00:00
-- url     : https://prove2.me/submissions/98bdabde-0426-410f-8047-15699842be91

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsifyWidthK_ProgMain
import Theorems.Thm_WidthK_ProgMain_mem_toFin
import Theorems.Thm_WidthK_ProgMain_nf_length_eq
import Theorems.Thm_WidthK_ProgMain_sat_toFin
import Theorems.Thm_WidthK_ProgMain_step_spec
import Theorems.Thm_WidthK_ProgMain_G_step
import Theorems.Thm_WidthK_ProgMain_card_le_of_clause
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Sparsify_exists_of_mem_leaves
import Theorems.Thm_Groundwork_Sparsify_iff_exists_mem_leaves
import Theorems.Thm_Groundwork_Sparsify_length_leaves_le
import Theorems.Thm_Groundwork_Sparsify_sat_red
import Theorems.Thm_Groundwork_Sparsify_stack_bound
import Theorems.Thm_Groundwork_Sparsify_step_eq_none_of_mem_leaves
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
section
open WidthK WidthK.ProgMain
open Finset Groundwork Groundwork.Sparsify WidthK.Prog
variable {θ : ℕ → ℕ} {k D T q leafB : ℕ} {Ok : Finset (Finset PLit) → Prop}
  {Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop}
namespace WidthK.ProgMain
theorem _root_.solution (hI : Iface θ k D T q leafB Ok Node) (hR : Refines θ k) {n hv : ℕ} (hT : T < (hv + 1) * q) (ψ : PFml)
    (hOk : Ok (toFin ψ)) (hψ : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    let L := leaves (stepK θ k) D (rootP ψ)
    L.length ≤ ∑ j ∈ range (hv + 1), D.choose j ∧
    (∀ x ∈ L, stepK θ k x = none ∧ x.length ≤ leafB ∧ ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧
    (∀ v : PLit → Prop, (∀ C ∈ ψ, ∃ a ∈ C, v a) ↔ ∃ x ∈ L, ∀ C ∈ x, ∃ a ∈ C, v a) ∧
    ∀ i, ((round (stepK θ k))^[i] ([rootP ψ], [])).1.length ≤ D + 1 ∧
      ∀ x ∈ ((round (stepK θ k))^[i] ([rootP ψ], [])).1, x.length ≤ ψ.length * 2 ^ k ∧
        ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n := by
  intro L
  have hb : ∀ s p t, G Node ψ s p t → p ≤ D ∧ t ≤ T := fun s p t h => hI.bound _ _ _ _ h.2
  have hs := G_step hI hR ψ
  have hr : G Node ψ (rootP ψ) 0 0 := ⟨hR.nf_root ψ, by rw [hR.toFin_root]; exact hI.root _ hOk⟩
  have hnone := step_eq_none_of_mem_leaves hb hs D (rootP ψ) 0 0 hr (by omega)
  have hk0 : ∀ C ∈ toFin ψ, C.card ≤ k := by
    intro X hX
    obtain ⟨C, hC, rfl⟩ := mem_toFin.1 hX
    exact (List.toFinset_card_le C).trans (hψ C hC).1
  have hcl : ∀ x p t, G Node ψ x p t → ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n := by
    intro x p t hx C hC
    obtain ⟨X₀, hX₀, hsub⟩ := hI.clause _ _ _ _ hx.2 _ (mem_toFin.2 ⟨C, hC, rfl⟩)
    obtain ⟨C₀, hC₀, rfl⟩ := mem_toFin.1 hX₀
    refine ⟨?_, fun l hl => (hψ C₀ hC₀).2 l (List.mem_toFinset.1 (hsub (List.mem_toFinset.2 hl)))⟩
    rw [← List.toFinset_card_of_nodup (hx.1.1 C hC)]
    exact (card_le_card hsub).trans (hk0 _ hX₀)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact length_leaves_le hb hs _ _ _ _ 0 0 hr (by omega) (by omega)
  · intro x hx
    obtain ⟨p', t', hx'⟩ := exists_of_mem_leaves hs _ _ 0 0 hr x hx
    refine ⟨hnone x hx, ?_, hcl x p' t' hx'⟩
    rw [nf_length_eq hx'.1]
    refine hI.leaf _ _ _ _ hx'.2 (hR.none x hx'.1 ?_)
    have := hnone x hx
    simpa [stepK] using this
  · intro v
    have h0 : (∀ C ∈ ψ, ∃ a ∈ C, v a) ↔ ∀ C ∈ rootP ψ, ∃ a ∈ C, v a := by
      rw [← sat_toFin, ← sat_toFin, hR.toFin_root, sat_red]
    rw [h0]
    refine iff_exists_mem_leaves hs (fun s => ∀ C ∈ s, ∃ a ∈ C, v a) ?_ _ _ 0 0 hr
    intro s p t l h hn hst
    obtain ⟨j, H, hrule, hl, hh, -, -⟩ := step_spec hI hR hn hst
    have := hI.sat _ _ _ _ _ _ v hn.2 hrule
    rwa [← hl, ← hh, sat_toFin, sat_toFin, sat_toFin] at this
  · intro i
    obtain ⟨h1, h2⟩ := stack_bound hb hs (rootP ψ) 0 0 hr i
    refine ⟨h1, fun x hx => ?_⟩
    obtain ⟨p', t', hx'⟩ := h2 x hx
    refine ⟨?_, hcl x p' t' hx'⟩
    rw [nf_length_eq hx'.1]
    refine (card_le_of_clause hk0 (hI.clause _ _ _ _ hx'.2)).trans (Nat.mul_le_mul_right _ ?_)
    rw [toFin]
    exact (List.toFinset_card_le _).trans (by simp)
end WidthK.ProgMain

-- Prove2me | solution 1 for SparsificationLemma.node_facts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:24:40.985925+00:00
-- url     : https://prove2.me/submissions/2bf3afae-8370-4555-9630-1c656a0f68fe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_StepSparsifyDefs
import Definitions.Def_SparsificationLemma_Iface
import Definitions.Def_SparsificationLemma_Shrink
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_PaddedDescent_F_MarkDeg
import Definitions.Def_PaddedDescent_F_MarkDeg
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSatRate_Leaf
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_SparsificationLemma_Nodes
import Theorems.Thm_SparsificationLemma_forall_nodesOf
import Theorems.Thm_CountKSat_ProgC_pick_spec
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
import Theorems.Thm_SparsificationLemma_Bound_bound
import Theorems.Thm_SparsificationLemma_Gen_length_rootP_le
import Theorems.Thm_SparsificationLemma_Gen_ok_of
import Theorems.Thm_SparsificationLemma_Shrink_length_step_le
import Theorems.Thm_SparsificationLemma_stIfaceC
import Theorems.Thm_UniformInK_Bound_bound
import Theorems.Thm_WidthK_Node_bound
import Theorems.Thm_WidthK_ProgMain_G_step
import Theorems.Thm_WidthK_ProgMain_mem_toFin
import Theorems.Thm_WidthK_Refine_mem_toFin
import Theorems.Thm_WidthK_Refine_stRefines
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
open SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK
namespace SparsificationLemma
theorem _root_.solution {k τ n : ℕ} {θ β : ℕ → ℕ} {ψ : PFml} (hT : ThrC k τ θ β) (hψ : IsKCNF k n ψ) (D : ℕ) :
    ∀ x ∈ nodesOf (stepC θ k) D (root ψ), NF x.1 ∧ Reduced (toFin x.1) ∧ IsKCNF k n x.1 ∧ x.1.length ≤ ψ.length ∧ (∀ C ∈ x.2, ∃ l, C = [l] ∧ l.1 < n) ∧
      x.2.length * τ ≤ k * ((k - 1) * n) := by
  have hθ : ∀ i, 1 ≤ θ i := hT.pos
  have hI := stIfaceC k τ n _ θ β hT (le_refl _)
  have hR := Refine.stRefines θ k hθ
  have hOk := Gen.ok_of hψ
  have hψ' : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n := fun C hC => (hψ C hC).2
  have key := forall_nodesOf (stepC θ k)
    (I := fun x => (∃ p t, ProgMain.G (fun F₀ F p t => ProgMain.Ok k n F₀ ∧ NodeU θ k τ F₀ F p t) ψ x.1 p t ∧ x.2.length * τ ≤ k * t) ∧ x.1.length ≤ ψ.length ∧
      ∀ C ∈ x.2, ∃ l, C = [l] ∧ l.1 < n) (by
      rintro s l h ⟨⟨p, t, hG, hlt⟩, hlen, hside⟩ hst
      obtain ⟨⟨H, P⟩, hp, he⟩ := Option.map_eq_some_iff.1 hst
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      have hK : stepK θ k s.1 = some (addP [H] s.1, addP P s.1) := by simp [stepK, hp]
      obtain ⟨g1, g2⟩ := ProgMain.G_step hI hR ψ s.1 p t _ _ hG hK
      obtain ⟨-, N, a, hh, hInv, -⟩ := hG.2.2
      obtain ⟨l1, l2⟩ := Shrink.length_step_le hθ hG.1 hInv.red hst
      obtain ⟨hHk, hHn⟩ := ProgC.pick_spec hθ hI hR hψ' hG hp
      refine ⟨⟨⟨_, _, g1, hlt⟩, l1.trans hlen, hside⟩, ⟨⟨_, _, g2, ?_⟩, l2.trans hlen, fun C hC => ?_⟩⟩
      · show (negU H ++ s.2).length * τ ≤ k * (t + τ)
        rw [List.length_append, negU, List.length_map, Nat.add_mul, Nat.mul_add]
        have := Nat.mul_le_mul_right τ hHk
        omega
      · rcases List.mem_append.1 hC with hC | hC
        · obtain ⟨ω, hω, rfl⟩ := List.mem_map.1 hC
          exact ⟨_, rfl, hHn ω hω⟩
        · exact hside C hC) D (root ψ)
    ⟨⟨0, 0, ⟨hR.nf_root ψ, show ProgMain.Ok k n (toFin ψ) ∧ NodeU θ k τ (toFin ψ) (toFin (rootP ψ)) 0 0 by rw [hR.toFin_root]; exact hI.root _ hOk⟩, by simp [root]⟩,
      Gen.length_rootP_le ψ, by simp [root]⟩
  intro x hx
  obtain ⟨⟨p, t, hG, hlt⟩, hlen, hside⟩ := key x hx
  have hb := (hI.bound _ _ _ _ hG.2).2
  obtain ⟨hnf, hok, hsub, N, a, hh, hInv, -⟩ := hG
  refine ⟨hnf, hInv.red, fun C hC => ?_, hlen, hside, hlt.trans (Nat.mul_le_mul_left _ hb)⟩
  obtain ⟨C', hC', hs, hne⟩ := hsub _ (ProgMain.mem_toFin.2 ⟨C, hC, rfl⟩)
  obtain ⟨b1, b2, b3⟩ := hok C' hC'
  refine ⟨(List.toFinset_nonempty_iff C).1 (hne b2), ?_, fun l hl => ?_⟩
  · rw [← List.toFinset_card_of_nodup (hnf.1 C hC)]
    exact (card_le_card hs).trans b3
  · have := b1 (hs (List.mem_toFinset.2 hl))
    rw [ProgMain.litsBelow, Finset.mem_product, Finset.mem_range] at this
    exact this.1
end SparsificationLemma

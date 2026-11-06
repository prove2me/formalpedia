-- Prove2me | solution 1 for SparsificationLemma.Gen.withSideClauses
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:16:20.696269+00:00
-- url     : https://prove2.me/submissions/6dc83e3f-67fd-4eac-8127-72a9ae7a55b6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_CountKSatRate_Tree
import Definitions.Def_SparsificationLemma_Iface
import Definitions.Def_SparsificationLemma_Shrink
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_PaddedDescent_F_MarkDeg
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Gen
import Theorems.Thm_SparsificationLemma_Gen_ok_of
import Theorems.Thm_SparsificationLemma_Gen_length_rootP_le
import Theorems.Thm_CountKSatRate_Tree_GT_step
import Theorems.Thm_CountKSatRate_Tree_sideT_taut
import Theorems.Thm_CountKSatRate_Tree_tree_of
import Theorems.Thm_CountKSat_stRootCount
import Theorems.Thm_CountKSat_stStepCount
import Theorems.Thm_CountKSat_stSumLeaves
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Sparsify_exists_of_mem_leaves
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
import Theorems.Thm_PaddedDescent_F_Mark_Deg_length_occ_le_of_none
import Theorems.Thm_SparsificationLemma_Shrink_length_step_le
import Theorems.Thm_SparsificationLemma_stIfaceC
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
open PaddedDescent.F.Mark (occ)
open SparsificationLemma.Gen
variable {k τ n D : ℕ} {θ β : ℕ → ℕ} {ψ : PFml}
namespace SparsificationLemma.Gen
theorem _root_.solution (hτ : 1 ≤ τ) (hT : ThrC k τ θ β) (hD : (∑ i ∈ range k, β i) * n ≤ D) (hψ : IsKCNF k n ψ) {B : ℕ}
    (hB : n * τ + k * ((k - 1) * n) ≤ B * τ) :
    (leaves (stepC θ k) D (rootP ψ, taut n)).length ≤ ∑ j ∈ range ((k - 1) * n / τ + 1), D.choose j ∧
    (∀ x ∈ leaves (stepC θ k) D (rootP ψ, taut n),
      stepC θ k x = none ∧ (leafF x).length ≤ (2 * ∑ j ∈ range k, θ j) * n + B ∧
        (∀ C ∈ x.1, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ (∀ v, (occ x.1 v).length ≤ 2 * ∑ j ∈ range k, θ j) ∧
        (∀ C ∈ x.2, (C ∈ taut n ∨ ∃ l, C = [l]) ∧ ∀ l ∈ C, l.1 < n) ∧ x.1.length ≤ ψ.length) ∧
    ∀ i, ((round (stepC θ k))^[i] ([(rootP ψ, taut n)], [])).1.length ≤ D + 1 ∧
      ∀ x ∈ ((round (stepC θ k))^[i] ([(rootP ψ, taut n)], [])).1,
        x.1.length ≤ ψ.length * 2 ^ k ∧ x.2.length ≤ B ∧ (∀ C ∈ x.1, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ C ∈ x.2, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n := by
  have hθ : ∀ i, 1 ≤ θ i := hT.pos
  have hI := stIfaceC k τ n D θ β hT hD
  have hR := Refine.stRefines θ k hθ
  have hOk := ok_of hψ
  have hψ' : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n := fun C hC => (hψ C hC).2
  have hT' : (k - 1) * n < ((k - 1) * n / τ + 1) * τ := by
    calc (k - 1) * n < τ * ((k - 1) * n / τ + 1) := Nat.lt_mul_div_succ _ (by omega : 0 < τ)
      _ = ((k - 1) * n / τ + 1) * τ := Nat.mul_comm _ _
  obtain ⟨c1, c2, -, c4⟩ := CountKSatRate.Tree.tree_of stStepCount stRootCount stSumLeaves hθ hI hR hT' hB ψ hOk hψ'
  have hs : ∀ (s : CNode) (p t : ℕ) (l h : CNode), InvL θ k τ n ψ s p t → stepC θ k s = some (l, h) →
      InvL θ k τ n ψ l (p + 1) t ∧ InvL θ k τ n ψ h (p + 1) (t + τ) := by
    intro s p t l h hG hst
    obtain ⟨g1, g2⟩ := CountKSatRate.Tree.GT_step hθ hI hR ψ hψ' s p t l h hG.1 hst
    obtain ⟨-, N, a, hh, hInv, -⟩ := hG.1.1.2.2
    obtain ⟨l1, l2⟩ := Shrink.length_step_le hθ hG.1.1.1 hInv.red hst
    exact ⟨⟨g1, l1.trans hG.2⟩, ⟨g2, l2.trans hG.2⟩⟩
  have hr : InvL θ k τ n ψ (rootP ψ, taut n) 0 0 :=
    ⟨⟨⟨hR.nf_root ψ, by rw [hR.toFin_root]; exact hI.root _ hOk⟩, CountKSatRate.Tree.sideT_taut n k τ⟩, length_rootP_le ψ⟩
  refine ⟨c1, fun x hx => ?_, c4⟩
  obtain ⟨d1, d2, d3, -⟩ := c2 x hx
  obtain ⟨p', t', hx', hlen⟩ := exists_of_mem_leaves hs _ _ 0 0 hr x hx
  have hne : ∀ C ∈ x.1, C ≠ [] := by
    intro C hC
    obtain ⟨C', hC', hsub, hne⟩ := hx'.1.2.2.1 _ (ProgMain.mem_toFin.2 ⟨C, hC, rfl⟩)
    obtain ⟨-, b, -⟩ := hx'.1.2.1 C' hC'
    exact (List.toFinset_nonempty_iff C).1 (hne b)
  have hst : stepK θ k x.1 = none := by simpa [stepC, stepK] using d1
  exact ⟨d1, d2, fun C hC => ⟨hne C hC, d3 C hC⟩,
    fun v => PaddedDescent.F.Mark.Deg.length_occ_le_of_none hθ hx'.1.1 (fun C hC => ⟨hne C hC, (d3 C hC).1⟩) hst v,
    fun C hC => ⟨hx'.2.2.2.2 C hC, (hx'.2.2.1 C hC).2⟩, hlen⟩
end SparsificationLemma.Gen

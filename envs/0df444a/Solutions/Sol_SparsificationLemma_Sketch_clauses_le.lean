-- Prove2me | solution 1 for SparsificationLemma.Sketch.clauses_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:37:40.538005+00:00
-- url     : https://prove2.me/submissions/5fbb63bf-6164-44cb-820d-04a4419944e0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_StepSparsifyDefs
import Definitions.Def_PaperSentencesStatement
import Definitions.Def_SparsificationLemma_Nodes
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsificationLemma_Len
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_ClauseBoundStatement
import Definitions.Def_CountKSatStatement
import Definitions.Def_PaddedDescent_F_MarkDeg
import Definitions.Def_PaddedDescent_F_MarkDeg
import Definitions.Def_SparsificationLemma_Sketch
import Theorems.Thm_CountKSatRate_Leaf_length_sideU_le
import Theorems.Thm_Groundwork_DecodeK_IsKCNF_length_le
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
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
import Theorems.Thm_Sat3_Is3CNF_length_le
import Theorems.Thm_SparsificationLemma_length_sideU_le
import Theorems.Thm_SparsificationLemma_mem_nodesOf_of_mem_leaves
import Theorems.Thm_SparsificationLemma_node_facts
import Theorems.Thm_SparsificationLemma_stGen
import Theorems.Thm_SparsificationLemma_stLenOfOcc
import Theorems.Thm_SparsificationLemma_stSide
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
open SparsificationLemma SparsificationLemma.Sketch
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK
namespace SparsificationLemma.Sketch
theorem _root_.solution {k τ n D : ℕ} {θ β : ℕ → ℕ} {ψ : PFml} (hk : 1 ≤ k) (hτ : 1 ≤ τ) (hT : ThrC k τ θ β) (hD : (∑ i ∈ range k, β i) * n ≤ D) (hψ : IsKCNF k n ψ) :
    ∀ x ∈ tree θ k D ψ, x.1.length ≤ (2 * ∑ j ∈ range k, θ j) * n ∧ (sideU x.2).length ≤ 2 * n ∧ (out x).length ≤ (2 * (∑ j ∈ range k, θ j) + 2) * n := by
  intro x hx
  obtain ⟨f1, -, f3, -, f5, -⟩ := node_facts hT hψ D x (mem_nodesOf_of_mem_leaves _ _ _ x hx)
  have hst : stepK θ k x.1 = none := by simpa [stepC, stepK] using (stGen stSide k τ n D θ β hk hτ hT hD ψ hψ).1 x hx
  have h1 : x.1.length ≤ (2 * ∑ j ∈ range k, θ j) * n :=
    stLenOfOcc k n _ x.1 f3 fun v => PaddedDescent.F.Mark.Deg.length_occ_le_of_none hT.pos f1 (fun C hC => ⟨(f3 C hC).1, (f3 C hC).2.1⟩) hst v
  have h2 : (sideU x.2).length ≤ 2 * n := length_sideU_le fun C hC l hl => by
    obtain ⟨l', rfl, hl'⟩ := f5 C hC
    rwa [List.mem_singleton.1 hl]
  refine ⟨h1, h2, ?_⟩
  have h3 : (out x).length ≤ (sideU x.2).length + x.1.length := by
    rw [← List.length_append]
    exact (List.dedup_sublist _).length_le
  rw [Nat.add_mul]
  omega
end SparsificationLemma.Sketch

-- Prove2me | solution 1 for SparsificationLemma.Mach.map_walkL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:54:54.77008+00:00
-- url     : https://prove2.me/submissions/b03fd78a-505a-4a2c-8913-40806e278829

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
import Theorems.Thm_SparsificationLemma_Mach_len_node_le
import Theorems.Thm_SparsificationLemma_Mach_len_state_le
import Theorems.Thm_CountKSatRate_Leaf_mem_sideU
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SparsificationLemma_Mach_out_of_stack
import Theorems.Thm_SparsificationLemma_Mach_total_le_leaves
import Theorems.Thm_SparsificationLemma_Mach_walkL_eq
import Theorems.Thm_SparsificationLemma_stOutputsSame
import Theorems.Thm_UniformInK_stIfaceU
import Theorems.Thm_UniformInK_stTreeU
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent PaddedDescent.F ClauseBound.Alg SparsificationLemma.Geo
namespace SparsificationLemma.Mach
theorem _root_.solution {k τ n L : ℕ} {ψ : PFml} {pad : U} (hk : 1 ≤ k) (h2 : k ^ 2 ≤ τ) (h8 : 8 * k ≤ τ) (hψ : IsKCNF k n ψ)
    (hL : ∑ j ∈ Finset.range (k * n / τ + 1), (bsumU τ k * n).choose j ≤ L) (hp1 : 2 * L ≤ pad.length + 1) (hp2 : L * (nodeLen k n ψ.length + 2) + 6 ≤ pad.length) :
    (walkL k pad τ (rootC (List.replicate n (), ψ))).map out = outTau k n τ ψ ∧ ∀ Φ ∈ outTau k n τ ψ, ∀ C ∈ Φ, ∀ l ∈ C, l.1 < n := by
  obtain ⟨t1, t2, -, t4⟩ := stTreeU stIfaceU k τ n hk h2 h8 ψ hψ
  have hO : (leaves (stepC (thetaU τ) k) (bsumU τ k * n) (rootC (List.replicate n (), ψ))).map out = outTau k n τ ψ := stOutputsSame (thetaU τ) k (bsumU τ k * n) n ψ
  obtain ⟨r, hr⟩ : ∃ r, r = rootC (List.replicate n (), ψ) := ⟨_, rfl⟩
  rw [← hr] at t1 t2 t4 hO ⊢
  have hd : ∀ x ∈ leaves (stepC (thetaU τ) k) (bsumU τ k * n) r, stepC (thetaU τ) k x = none := fun x hx => (t2 x hx).1
  have hnode : ∀ i, ∀ x ∈ ((round (stepC (thetaU τ) k))^[i] ([r], [])).1, len x ≤ nodeLen k n ψ.length := fun i x hx =>
    let ⟨a1, a2, a3, a4⟩ := (t4 i).2 x hx
    len_node_le a1 a2 a3 a4
  have hst : ∀ i, len ((round (stepC (thetaU τ) k))^[i] ([r], [])) ≤ pad.length := fun i =>
    (len_state_le ((total_le_leaves _ _ r hd i).trans (t1.trans hL)) (hnode i) (out_of_stack _ (fun x => len x ≤ nodeLen k n ψ.length) r hnode i)).trans hp2
  refine ⟨?_, ?_⟩
  · rw [walkL_eq k pad τ r _ hd (by have := t1.trans hL; omega) hst, hO]
  · rw [← hO]
    intro Φ hΦ C hC
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hΦ
    obtain ⟨-, -, b3, -, b5⟩ := t2 x hx
    rcases List.mem_append.1 (List.mem_dedup.1 hC) with hC | hC
    · exact (b5 C (Leaf.mem_sideU.1 hC).1).2
    · exact (b3 C hC).2.2
end SparsificationLemma.Mach

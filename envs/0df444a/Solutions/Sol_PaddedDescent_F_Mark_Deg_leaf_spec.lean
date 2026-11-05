-- Prove2me | solution 1 for PaddedDescent.F.Mark.Deg.leaf_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:06:06.244607+00:00
-- url     : https://prove2.me/submissions/c1cf2c0f-2f8c-4f7e-9b78-81561f0ac6ea

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_PaddedDescent_F_MarkDeg
import Theorems.Thm_PaddedDescent_F_Mark_Deg_length_occ_le_of_none
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Sparsify_exists_of_mem_leaves
import Theorems.Thm_Groundwork_Sparsify_step_eq_none_of_mem_leaves
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_WidthK_Node_bound
import Theorems.Thm_WidthK_ProgMain_G_step
import Theorems.Thm_WidthK_ProgMain_iface
import Theorems.Thm_WidthK_ProgMain_mem_toFin
import Theorems.Thm_WidthK_Refine_mem_toFin
import Theorems.Thm_WidthK_Refine_stRefines
import Theorems.Thm_WidthK_stBetaSum
import Theorems.Thm_WidthK_stHeavyEq
import Theorems.Thm_WidthK_stLeafCard
import Theorems.Thm_WidthK_stLightEq
import Theorems.Thm_WidthK_stNodeBound
import Theorems.Thm_WidthK_stNodeRoot
import Theorems.Thm_WidthK_stNodeStep
import Theorems.Thm_WidthK_stSatIff
import Theorems.Thm_WidthK_stThr
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Deg
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify
open WidthK (theta bsum leafC lay)
open WidthK.Prog (stepK NF toFin)
namespace PaddedDescent.F.Mark.Deg
theorem _root_.solution {τ : ℕ} (hτ : 1 ≤ τ) (k n : ℕ) (ψ : PFml) (hψ : ∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    ∀ x ∈ leaves (stepK (theta τ) k) (bsum τ k * n) (rootP ψ), NF x ∧ (∀ C ∈ x, C ≠ []) ∧ ∀ v, (occ x v).length ≤ leafC τ k := by
  have hθ : ∀ i, 1 ≤ theta τ i := (WidthK.stThr τ hτ).pos
  have hI := WidthK.ProgMain.iface WidthK.stNodeRoot WidthK.stNodeStep WidthK.stNodeBound WidthK.stLeafCard WidthK.stLightEq
    WidthK.stHeavyEq WidthK.stSatIff WidthK.stThr WidthK.stBetaSum hτ k n
  have hR := WidthK.Refine.stRefines _ k hθ
  have hOk : WidthK.ProgMain.Ok k n (toFin ψ) := by
    intro X hX
    obtain ⟨C, hC, rfl⟩ := WidthK.ProgMain.mem_toFin.1 hX
    obtain ⟨a, b, c⟩ := hψ C hC
    refine ⟨fun l hl => ?_, (List.toFinset_nonempty_iff C).2 a, (List.toFinset_card_le C).trans b⟩
    rw [WidthK.ProgMain.litsBelow, Finset.mem_product, Finset.mem_range]
    exact ⟨c l (List.mem_toFinset.1 hl), Finset.mem_univ _⟩
  have hb : ∀ s p t, WidthK.ProgMain.G (fun F₀ F p t => WidthK.ProgMain.Ok k n F₀ ∧ WidthK.Node (theta τ) k τ F₀ F p t) ψ s p t →
      p ≤ bsum τ k * n ∧ t ≤ k * n := fun s p t h => hI.bound _ _ _ _ h.2
  have hs := WidthK.ProgMain.G_step hI hR ψ
  have hr : WidthK.ProgMain.G (fun F₀ F p t => WidthK.ProgMain.Ok k n F₀ ∧ WidthK.Node (theta τ) k τ F₀ F p t) ψ (rootP ψ) 0 0 :=
    ⟨hR.nf_root ψ, by rw [hR.toFin_root]; exact hI.root _ hOk⟩
  have hnone := step_eq_none_of_mem_leaves hb hs (bsum τ k * n) (rootP ψ) 0 0 hr (by omega)
  intro x hx
  obtain ⟨p', t', hx'⟩ := exists_of_mem_leaves hs _ _ 0 0 hr x hx
  have hcl : ∀ C ∈ x, C ≠ [] ∧ C.length ≤ k := by
    intro C hC
    obtain ⟨C', hC', hsub, hne⟩ := hx'.2.2.1 _ (WidthK.ProgMain.mem_toFin.2 ⟨C, hC, rfl⟩)
    obtain ⟨-, b, c⟩ := hx'.2.1 C' hC'
    refine ⟨(List.toFinset_nonempty_iff C).1 (hne b), ?_⟩
    rw [← List.toFinset_card_of_nodup (hx'.1.1 C hC)]
    exact (card_le_card hsub).trans c
  exact ⟨hx'.1, fun C hC => (hcl C hC).1, fun v => length_occ_le_of_none hθ hx'.1 hcl (hnone x hx) v⟩
end PaddedDescent.F.Mark.Deg

-- Prove2me | solution 1 for SparsificationLemma.TreeWalk.leaf_ne_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:37:33.758018+00:00
-- url     : https://prove2.me/submissions/0d685c44-e686-4451-a72d-14265d620b42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Geo_Defs
import Definitions.Def_WidthK_Top_Sat
import Definitions.Def_SparsificationLemma_Geo_Thr
import Definitions.Def_SparsificationLemma_Geo_Tau
import Definitions.Def_SparsificationLemma_Geo_Eps
import Definitions.Def_SparsificationLemma_Iface
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_UniformInK_Spars_Thresholds
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsificationLemma_TreeWalk_Walk
import Theorems.Thm_SparsificationLemma_TreeWalk_iface
import Theorems.Thm_Groundwork_Sparsify_exists_of_mem_leaves
import Theorems.Thm_SparsificationLemma_Gen_ok_of
import Theorems.Thm_SparsificationLemma_Geo_stThrGeo
import Theorems.Thm_WidthK_ProgMain_G_step
import Theorems.Thm_WidthK_ProgMain_iface
import Theorems.Thm_WidthK_ProgMain_mem_toFin
import Theorems.Thm_WidthK_Refine_mem_toFin
import Theorems.Thm_WidthK_Refine_stRefines


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.TreeWalk
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat UniformInK SparsificationLemma.Geo
open Groundwork.Prog.SatTopK (Sparsifies)
variable {k τ : ℕ}
namespace SparsificationLemma.TreeWalk
theorem _root_.solution (hk : 1 ≤ k) (hτ : 8 * k ≤ τ) {n : ℕ} {ψ : PFml} (hψ : IsKCNF k n ψ) (D : ℕ) :
    ∀ x ∈ leaves (stepK (thetaU τ) k) D (rootP ψ), ∀ C ∈ x, C ≠ [] := by
  intro x hx C hC
  have hI := iface hk hτ n
  have hR := Refine.stRefines _ k (stThrGeo k τ hk hτ).pos
  obtain ⟨p, t, hx'⟩ := exists_of_mem_leaves (ProgMain.G_step hI hR ψ) D (rootP ψ) 0 0
    ⟨hR.nf_root ψ, by rw [hR.toFin_root]; exact hI.root _ (Gen.ok_of hψ)⟩ x hx
  obtain ⟨C', hC', -, hne⟩ := hx'.2.2.1 _ (ProgMain.mem_toFin.2 ⟨C, hC, rfl⟩)
  exact (List.toFinset_nonempty_iff C).1 (hne (hx'.2.1 C' hC').2.1)
end SparsificationLemma.TreeWalk

-- Prove2me | solution 1 for SparsificationLemma.TreeWalk.lemSparsification_walk_k
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:59:05.752998+00:00
-- url     : https://prove2.me/submissions/ccd7a587-af0b-4fe7-80b0-3f0be2f7da87

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
import Theorems.Thm_SparsificationLemma_TreeWalk_sparsifies_tau
import Theorems.Thm_SparsificationLemma_TreeWalk_leaf_ne_nil
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SparsificationLemma_Geo_stTauE


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.TreeWalk
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat UniformInK SparsificationLemma.Geo
open Groundwork.Prog.SatTopK (Sparsifies)
variable {k τ : ℕ}
namespace SparsificationLemma.TreeWalk
theorem _root_.solution (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℕ, 8 * k ≤ τ ∧ Sparsifies k ε (stepK (thetaU τ) k) rootP (bsumU τ k) (leafCU τ k) (2 ^ k) ∧
      ∀ (n : ℕ) (ψ : PFml), IsKCNF k n ψ → ∀ x ∈ leaves (stepK (thetaU τ) k) (bsumU τ k * n) (rootP ψ), ∀ C ∈ x, C ≠ [] := by
  obtain ⟨q, hq0, hq1⟩ := exists_rat_btwn (lt_min hε one_pos)
  have h0 : 0 < q := by exact_mod_cast hq0
  have h1 : q ≤ 1 := by exact_mod_cast (hq1.trans_le (min_le_right _ _)).le
  obtain ⟨a, b, -⟩ := stTauE k q hk h0 h1
  exact ⟨tauE k q, a, sparsifies_tau hk a (b.trans (hq1.trans_le (min_le_left _ _)).le), fun n ψ hψ => leaf_ne_nil hk a hψ _⟩
end SparsificationLemma.TreeWalk

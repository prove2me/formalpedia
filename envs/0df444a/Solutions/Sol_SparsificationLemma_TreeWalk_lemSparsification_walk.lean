-- Prove2me | solution 1 for SparsificationLemma.TreeWalk.lemSparsification_walk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:13:06.028808+00:00
-- url     : https://prove2.me/submissions/d6792282-f7f5-4190-808a-a3dbe45b01ad

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
import Theorems.Thm_SparsificationLemma_TreeWalk_lemSparsification_walk_k

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.TreeWalk
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat UniformInK SparsificationLemma.Geo
open Groundwork.Prog.SatTopK (Sparsifies)
variable {k τ : ℕ}
namespace SparsificationLemma.TreeWalk
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℕ, 24 ≤ τ ∧ Sparsifies 3 ε (stepK (thetaU τ) 3) rootP (bsumU τ 3) (leafCU τ 3) 8 ∧
      ∀ (n : ℕ) (ψ : PFml), IsKCNF 3 n ψ → ∀ x ∈ leaves (stepK (thetaU τ) 3) (bsumU τ 3 * n) (rootP ψ), ∀ C ∈ x, C ≠ [] :=
  lemSparsification_walk_k (le_of_lt (by norm_num : 1 < 3)) hε
end SparsificationLemma.TreeWalk

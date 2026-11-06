-- Prove2me | solution 1 for SparsificationLemma.TreeWalk.iface
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:16:45.112205+00:00
-- url     : https://prove2.me/submissions/c1d993a3-fa8d-47c5-8ed5-f2f71b5b05e4

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
import Theorems.Thm_SparsificationLemma_Geo_stThrGeo
import Theorems.Thm_SparsificationLemma_stIfaceC
import Theorems.Thm_UniformInK_stBetaSumU


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.TreeWalk
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat UniformInK SparsificationLemma.Geo
open Groundwork.Prog.SatTopK (Sparsifies)
variable {k τ : ℕ}
namespace SparsificationLemma.TreeWalk
theorem _root_.solution (hk : 1 ≤ k) (hτ : 8 * k ≤ τ) (n : ℕ) :
    Iface (thetaU τ) k (bsumU τ k * n) ((k - 1) * n) τ ((2 * ∑ j ∈ range k, thetaU τ j) * n) (ProgMain.Ok k n)
      (fun F₀ F p t => ProgMain.Ok k n F₀ ∧ NodeU (thetaU τ) k τ F₀ F p t) :=
  stIfaceC k τ n (bsumU τ k * n) (thetaU τ) (betaSU τ) (stThrGeo k τ hk hτ) (Nat.mul_le_mul_right _ (stBetaSumU τ k (by omega)))
end SparsificationLemma.TreeWalk

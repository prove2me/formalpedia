-- Prove2me | solution 1 for ThreeSatOnTree.one_le_leafCU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:20:35.742917+00:00
-- url     : https://prove2.me/submissions/914a5e43-3dd3-41ec-8411-e09c8c952de2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatOnTree_Defs
import Definitions.Def_Eight_SecProof_Proof
import Definitions.Def_SparsificationLemma_TreeWalk_Walk
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_WidthK_Top_Poly
import Definitions.Def_WidthK_Poly_Decode
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_ThreeSatOnTree_ThmEveryDelta

set_option autoImplicit false
section
section
open ThreeSatOnTree
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK Groundwork.Sparsify WidthK.Prog UniformInK Paper Eight SparsificationLemma.TreeWalk
namespace ThreeSatOnTree
theorem _root_.solution (τ : ℕ) : (1 : ℝ) ≤ (leafCU τ 3 : ℝ) := by
  have h : leafCU τ 3 = 2 * ∑ j ∈ Finset.range 3, thetaU τ j := rfl
  have h0 : thetaU τ 0 = 1 := rfl
  have : 1 ≤ leafCU τ 3 := by
    rw [h, Finset.sum_range_succ', h0]
    omega
  exact_mod_cast this
end ThreeSatOnTree

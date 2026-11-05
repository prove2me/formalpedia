-- Prove2me | solution 1 for SparsificationLemma.Mach.eL_encIn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:01:21.464593+00:00
-- url     : https://prove2.me/submissions/4ab77748-3642-4754-98e8-4c303e10effc

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
import Theorems.Thm_SparsificationLemma_Mach_dec_encIn
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent PaddedDescent.F ClauseBound.Alg SparsificationLemma.Geo
namespace SparsificationLemma.Mach
theorem _root_.solution (s k n : ℕ) (φ : Sat3.CNF n) (hk : 1 ≤ k) (hφ : ∀ C ∈ φ, C.length ≤ k) :
    eL (encIn s k φ) = n / 2 ^ s + k + 3 * Nat.size (encIn s k φ).length + 9 := by
  obtain ⟨d1, d2, d3⟩ := dec_encIn s k n φ hk hφ
  rw [eL, d1, d2, d3, List.length_replicate]
end SparsificationLemma.Mach

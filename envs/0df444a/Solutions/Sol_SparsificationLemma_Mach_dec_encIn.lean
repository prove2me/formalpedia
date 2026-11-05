-- Prove2me | solution 1 for SparsificationLemma.Mach.dec_encIn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:57:47.061731+00:00
-- url     : https://prove2.me/submissions/814f0c63-3f86-4847-a145-8cb76f4e180d

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
import Theorems.Thm_ClauseBound_Alg_Decode_kOf_ones
import Theorems.Thm_ClauseBound_Alg_Decode_restOf_ones
import Theorems.Thm_ClauseBound_Alg_Decode_stDecM
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
    sL (encIn s k φ) = s ∧ kL (encIn s k φ) = k ∧ dL (encIn s k φ) = (List.replicate n (), Decode.toN φ) := by
  obtain ⟨h1, h2⟩ := ClauseBound.Alg.Decode.stDecM k n φ hk hφ
  refine ⟨?_, ?_, ?_⟩
  · rw [sL, encIn, ClauseBound.Alg.Decode.kOf_ones, List.length_replicate]
  · rw [kL, encIn, ClauseBound.Alg.Decode.restOf_ones, h1, List.length_replicate]
  · rw [dL, encIn, ClauseBound.Alg.Decode.restOf_ones, h2]
end SparsificationLemma.Mach

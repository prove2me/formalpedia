-- Prove2me | solution 1 for SparsificationLemma.Mach.codeP_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:39:44.869052+00:00
-- url     : https://prove2.me/submissions/6af7a3a0-c386-4d80-8d4f-3adce90e45ef

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
import Theorems.Thm_SparsificationLemma_Mach_codeNatP_eq
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent PaddedDescent.F ClauseBound.Alg SparsificationLemma.Geo
namespace SparsificationLemma.Mach
theorem _root_.solution {pad : U} {L : List PFml} (h : ∀ Φ ∈ L, ∀ C ∈ Φ, ∀ l ∈ C, l.1 ≤ pad.length) : codeP pad L = code L := by
  unfold codeP code
  congr 1
  refine List.flatMap_congr fun Φ hΦ => ?_
  unfold codeFmlP codeFml
  congr 2
  refine List.flatMap_congr fun C hC => ?_
  unfold codeClP codeCl
  congr 2
  refine List.flatMap_congr fun l hl => ?_
  rw [codeLitP, codeLit, codeNatP_eq (h Φ hΦ C hC l hl)]
end SparsificationLemma.Mach

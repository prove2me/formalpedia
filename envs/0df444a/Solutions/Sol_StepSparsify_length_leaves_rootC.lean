-- Prove2me | solution 1 for StepSparsify.length_leaves_rootC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:47:32.953851+00:00
-- url     : https://prove2.me/submissions/4f885806-ba9b-4ed9-b749-93ef1af4bae1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_StepSparsify_CalNumbers
import Definitions.Def_StepSparsify_CalLeaves
import Definitions.Def_StepSparsify_CertThCal
import Definitions.Def_SparsificationLemma_Cal_Thr
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_UniformInK_Cert_Sparsify
import Definitions.Def_CountKSat_Poly
import Definitions.Def_StepSparsify_CalServes
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_SparsificationLemma_stSide
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open StepSparsify
open Finset Groundwork Groundwork.Sparsify WidthK.Prog CountKSat CountKSat.Poly PaddedDescent UniformInK UniformInK.CertSparsify SparsificationLemma
namespace StepSparsify
theorem _root_.solution (θ : ℕ → ℕ) (k D n : ℕ) (ψ : PFml) :
    (leaves (stepC θ k) D (rootC (List.replicate n (), ψ))).length = (tree θ k D ψ).length := by
  rw [rootC, stSide, List.length_map, tree, root]
end StepSparsify

-- Prove2me | solution 1 for StepSparsify.length_noTaut_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:49:49.260947+00:00
-- url     : https://prove2.me/submissions/780eb0e2-197c-49eb-9046-fffb4d54c76e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_StepSparsify_Walk
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_UniformInK_Tree_Stack
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSatRate_Top
import Definitions.Def_CountKSatRate_Top
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_StepSparsify_WalkCount
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open StepSparsify
open Finset Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Top ClauseBound.TopN UniformInK SparsificationLemma
open Groundwork.Sparsify (PFml leaves round)
namespace StepSparsify
theorem _root_.solution (ψ : PFml) : (noTaut ψ).length ≤ ψ.length := List.length_filter_le _ _
end StepSparsify

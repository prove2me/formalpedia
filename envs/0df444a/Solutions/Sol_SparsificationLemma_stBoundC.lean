-- Prove2me | solution 1 for SparsificationLemma.stBoundC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:56:42.231265+00:00
-- url     : https://prove2.me/submissions/88fa595a-2ab5-4967-b971-402f885ac208

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_UniformInK_Spars_Bound
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Bound
import Theorems.Thm_SparsificationLemma_Bound_bound
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_UniformInK_Bound_bound
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open SparsificationLemma
open Finset Groundwork Groundwork.Sparsify WidthK UniformInK
namespace SparsificationLemma
theorem _root_.solution : StBoundC := fun _ _ _ _ _ _ _ _ _ _ _ _ hT hU hφ h => Bound.bound hT hU hφ h
end SparsificationLemma

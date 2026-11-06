-- Prove2me | solution 2 for UniformInK.stNodeBoundU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:42:29.013243+00:00
-- url     : https://prove2.me/submissions/02598b93-dd5f-4ff4-b597-b793b3d1c286

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_StepMachines_Math_Sparsify
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_UniformInK_Spars_Bound
import Theorems.Thm_UniformInK_Bound_bound
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK
namespace UniformInK
theorem _root_.solution : StNodeBoundU := fun _ _ _ _ _ _ _ _ _ _ _ _ hT hU hφ h => Bound.bound hT hU hφ h
end UniformInK

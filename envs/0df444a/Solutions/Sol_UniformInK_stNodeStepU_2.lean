-- Prove2me | solution 2 for UniformInK.stNodeStepU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:02:45.864192+00:00
-- url     : https://prove2.me/submissions/9a60a7dd-6230-447f-a9b3-f3660792a144

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_Step
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.SplitIfs
import Definitions.Def_UniformInK_Spars_Step
import Theorems.Thm_UniformInK_Step_node_light
import Theorems.Thm_UniformInK_Step_node_heavy
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK
namespace UniformInK
theorem _root_.solution : StNodeStepU := fun _ _ _ _ _ _ _ _ _ _ _ hθ h hB => ⟨Step.node_light hθ h hB, Step.node_heavy hθ h hB⟩
end UniformInK

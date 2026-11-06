-- Prove2me | solution 1 for UniformInK.stNodeRootU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:47:30.678146+00:00
-- url     : https://prove2.me/submissions/f0c15ac9-95c8-4168-aef5-706b96a70444

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_Step
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.SplitIfs
import Definitions.Def_UniformInK_Spars_Step
import Theorems.Thm_UniformInK_Step_node_root
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_Sparsify_node_root
import Theorems.Thm_WidthK_node_root
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK
namespace UniformInK
theorem _root_.solution : StNodeRootU := fun _ _ θ k τ φ => Step.node_root θ k τ φ
end UniformInK

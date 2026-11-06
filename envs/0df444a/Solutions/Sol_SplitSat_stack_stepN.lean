-- Prove2me | solution 1 for SplitSat.stack_stepN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:41:37.762303+00:00
-- url     : https://prove2.me/submissions/26ff723f-4523-4756-aee0-bfc6aa433498

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Mathlib.Tactic
import Definitions.Def_SplitSat_Sizes
import Theorems.Thm_SplitSat_round_stepN_iterate
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_WidthK_InvK_step
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Sparsify
namespace SplitSat
theorem _root_.solution (step : Fml → Option (Fml × Fml)) (u : List Unit) (i : ℕ) (x : Fml) :
    ((Sparsify.round (stepN step))^[i] ([((u, x) : NFml)], [])).1 = ((Sparsify.round step)^[i] ([x], [])).1.map fun y => ((u, y) : NFml) :=
  congrArg Prod.fst (round_stepN_iterate step u i ([x], []))
end SplitSat

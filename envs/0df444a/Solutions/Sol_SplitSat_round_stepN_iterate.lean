-- Prove2me | solution 1 for SplitSat.round_stepN_iterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:27:29.930461+00:00
-- url     : https://prove2.me/submissions/03d68806-d04d-4cf1-b6db-e75bae52b600

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Mathlib.Tactic
import Definitions.Def_SplitSat_Sizes
import Theorems.Thm_SplitSat_round_stepN
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_WidthK_InvK_step
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Sparsify
namespace SplitSat
theorem _root_.solution (step : Fml → Option (Fml × Fml)) (u : List Unit) (i : ℕ) (p : List Fml × List Fml) :
    (Sparsify.round (stepN step))^[i] (p.1.map fun y => ((u, y) : NFml), p.2.map fun y => ((u, y) : NFml)) =
      (((Sparsify.round step)^[i] p).1.map fun y => ((u, y) : NFml), ((Sparsify.round step)^[i] p).2.map fun y => ((u, y) : NFml)) := by
  induction i generalizing p with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, round_stepN, ih]
end SplitSat

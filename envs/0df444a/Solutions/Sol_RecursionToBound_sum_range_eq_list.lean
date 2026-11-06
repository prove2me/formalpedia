-- Prove2me | solution 1 for RecursionToBound.sum_range_eq_list
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:51:04.983206+00:00
-- url     : https://prove2.me/submissions/fe6552a3-239f-4ab3-a643-550fff1d6aa3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Definitions.Def_RecursionToBound_Cert_Numbers
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open RecursionToBound
open Finset SparsificationLemma
namespace RecursionToBound
theorem _root_.solution (f : ℕ → ℕ) (k : ℕ) : ∑ j ∈ range k, f j = ((List.range k).map f).sum := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
end RecursionToBound

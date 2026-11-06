-- Prove2me | solution 1 for RecursionToBound.occBound_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:06:12.400294+00:00
-- url     : https://prove2.me/submissions/c079a1bc-8020-4948-bebe-8105dc6e4d7f

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
import Theorems.Thm_RecursionToBound_sum_range_eq_list
import Theorems.Thm_ClauseBound_Boson_Dual_sum_range_eq_list
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
theorem _root_.solution (k : ℕ) (r : ℕ × ℕ) : occBound k r = 2 * ((List.range k).map (thresholds k r)).sum + 2 := by
  rw [occBound, sum_range_eq_list]
end RecursionToBound

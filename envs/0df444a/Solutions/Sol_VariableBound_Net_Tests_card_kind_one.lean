-- Prove2me | solution 1 for VariableBound.Net.Tests.card_kind_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:03:10.380037+00:00
-- url     : https://prove2.me/submissions/a042d972-dd34-4e0a-ba37-bbb94a27ca01

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_VariableBound_Net_Rank
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_VariableBound_Net_Tests
import Theorems.Thm_VariableBound_Net_Tests_card_kind_zero
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_VariableBound_Net_Basic_kind_cases
import Theorems.Thm_VariableBound_Net_Basic_length_objs
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Tests
open Groundwork Groundwork.Prog Finset
variable {k g n : ℕ} {D : Dat}
namespace VariableBound.Net.Tests
theorem _root_.solution (hW : WfD k n D) : #((range (objs D).length).filter fun o => (obAt D o).1 = 1) = (D.2.map List.length).sum := by
  have h1 := card_filter_add_card_filter_not (s := range (objs D).length) fun o => (obAt D o).1 = 0
  have h2 : ((range (objs D).length).filter fun o => ¬ (obAt D o).1 = 0) = (range (objs D).length).filter fun o => (obAt D o).1 = 1 := by
    refine filter_congr fun o ho => ?_
    have := Basic.kind_cases (D := D) (mem_range.1 ho)
    omega
  rw [h2, card_kind_zero hW, card_range] at h1
  have h3 := Basic.length_objs (D := D)
  omega
end VariableBound.Net.Tests

-- Prove2me | solution 1 for VariableBound.Net.Tests.sum_length_tst_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:49:46.552366+00:00
-- url     : https://prove2.me/submissions/22e0c395-09a5-46ad-a1e5-bdba97d760f5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_VariableBound_Net_Rank
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_VariableBound_Net_Tests
import Theorems.Thm_VariableBound_Net_Tests_sum_lt_eq_sum_product
import Theorems.Thm_P2M_VariableBound_Net_Tests_sum_length_tst_le__2d95f271980f
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Tests
open Groundwork Groundwork.Prog Finset
variable {k g n : ℕ} {D : Dat}
namespace VariableBound.Net.Tests
theorem _root_.solution (hW : WfD k n D) (κ : ℕ) :
    ∑ b ∈ range g, ∑ a ∈ range b, (tst g n D a b κ).length ≤ (k - 1 + κ) * #((range (objs D).length).filter fun o => (obAt D o).1 = κ) := by
  rw [sum_lt_eq_sum_product fun a b => (tst g n D a b κ).length]
  exact sum_length_tst_le' hW κ
end VariableBound.Net.Tests

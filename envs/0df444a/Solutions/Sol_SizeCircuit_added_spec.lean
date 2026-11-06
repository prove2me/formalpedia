-- Prove2me | solution 1 for SizeCircuit.added_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:00:13.803248+00:00
-- url     : https://prove2.me/submissions/1014d917-00b9-485c-b705-fba0130c1291

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Addition
import Theorems.Thm_SizeCircuit_iterate_spec
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks
namespace SizeCircuit
theorem _root_.solution (n : ℕ) : (added n).1 = [] ∧ (added n).2.1 = [] ∧ (∀ x ∈ (added n).2.2.1, x < n + (added n).2.2.2.length) ∧ WFa n (added n).2.2.2 ∧
    (added n).2.2.2.length ≤ 5 * n ∧ (added n).2.2.1.length ≤ n := by
  obtain ⟨g, h1, h2, h3⟩ := iterate_spec n n le_rfl
  exact ⟨List.length_eq_zero_iff.1 (by unfold added; omega), List.length_eq_zero_iff.1 (by unfold added; omega), g.2.2.1, g.2.2.2.1, h2, h3⟩
end SizeCircuit

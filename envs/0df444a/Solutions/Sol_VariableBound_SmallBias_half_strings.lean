-- Prove2me | solution 1 for VariableBound.SmallBias.half_strings
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:57:31.862611+00:00
-- url     : https://prove2.me/submissions/659d828a-3f01-47a6-b808-5d855d1170af

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Definitions.Def_VariableBound_Family_SmallBias
import Theorems.Thm_VariableBound_SmallBias_ip_add_right
import Theorems.Thm_VariableBound_SmallBias_ip_single

set_option autoImplicit false
section
section
open VariableBound VariableBound.SmallBias
open Finset AppVariables
variable {s : ℕ}
namespace VariableBound.SmallBias
theorem _root_.solution (x : Fin s → ZMod 2) (hx : x ≠ 0) : 2 * #{y : Fin s → ZMod 2 | ip x y = 1} = Fintype.card (Fin s → ZMod 2) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hi1 : x i = 1 := by
    have h : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
    exact h _ hi
  have hsw : #{y : Fin s → ZMod 2 | ip x y = 1} = #{y : Fin s → ZMod 2 | ¬ ip x y = 1} := by
    refine card_equiv (Equiv.addRight (Pi.single i 1)) fun y => ?_
    have h : ∀ c : ZMod 2, c = 1 ↔ ¬ c + 1 = 1 := by decide
    simp only [mem_filter, mem_univ, true_and, Equiv.coe_addRight, ip_add_right, ip_single, hi1]
    exact h _
  have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin s → ZMod 2))) (fun y => ip x y = 1)
  rw [card_univ] at hsum
  omega
end VariableBound.SmallBias

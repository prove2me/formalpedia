-- Prove2me | solution 1 for UniformInK.Bound.acc_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:22:06.625699+00:00
-- url     : https://prove2.me/submissions/544a2fe2-352b-494a-b527-14e96ed15008

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_StepMachines_Math_Sparsify
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_UniformInK_Spars_Bound
import Theorems.Thm_UniformInK_Bound_card_lay_le
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK
open UniformInK.Bound
variable {α : Type*} [DecidableEq α] {θ β : ℕ → ℕ} {k τ n : ℕ} {φ F N : Finset (Finset α)} {U : Finset α} {a : ℕ → ℕ} {p t : ℕ}
namespace UniformInK.Bound
theorem _root_.solution (hT : ThrU k τ θ β) (hU : U.card ≤ 2 * n) (hFU : ∀ C ∈ F, C ⊆ U) (h : InvU θ F N a) (ha0 : a 0 = 0) (i : ℕ) (hik : i < k) :
    a i ≤ β i * n := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [ha0]; exact Nat.zero_le _
    have h2 : ∑ i' ∈ range i, 2 * θ (i - i') * a i' ≤ (∑ i' ∈ range i, 2 * θ (i - i') * β i') * n := by
      rw [sum_mul]
      refine sum_le_sum fun i' hi' => ?_
      have hlt := mem_range.1 hi'
      rw [Nat.mul_assoc (2 * θ (i - i'))]
      exact Nat.mul_le_mul_left _ (ih i' hlt (hlt.trans hik))
    calc a i ≤ (lay N i).card + ∑ i' ∈ range i, 2 * θ (i - i') * a i' := h.acc i
      _ ≤ 4 * θ (i - 1) * n + (∑ i' ∈ range i, 2 * θ (i - i') * β i') * n := Nat.add_le_add (card_lay_le hU hFU h hi) h2
      _ = (4 * θ (i - 1) + ∑ i' ∈ range i, 2 * θ (i - i') * β i') * n := by rw [Nat.add_mul]
      _ ≤ β i * n := Nat.mul_le_mul_right _ (hT.step i hi hik)
end UniformInK.Bound

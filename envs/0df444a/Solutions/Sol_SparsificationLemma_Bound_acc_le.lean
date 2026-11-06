-- Prove2me | solution 1 for SparsificationLemma.Bound.acc_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:45:32.041035+00:00
-- url     : https://prove2.me/submissions/9e347365-049d-414a-a905-36b5a5ed65bf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_UniformInK_Spars_Bound
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Bound
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_Sparsify_card_ones_le
import Theorems.Thm_Groundwork_TM_Run_one
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_UniformInK_Bound_card_lay_le
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open SparsificationLemma
open Finset Groundwork Groundwork.Sparsify WidthK UniformInK
open SparsificationLemma.Bound
variable {α : Type*} [DecidableEq α] {θ β : ℕ → ℕ} {k τ n : ℕ} {φ F N : Finset (Finset α)} {U : Finset α} {a : ℕ → ℕ} {p t : ℕ}
namespace SparsificationLemma.Bound
theorem _root_.solution (hT : ThrC k τ θ β) (hU : U.card ≤ 2 * n) (hFU : ∀ C ∈ F, C ⊆ U) (h : InvU θ F N a) (ha0 : a 0 = 0) (i : ℕ) (hik : i < k) :
    a i ≤ β i * n := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    obtain rfl | rfl | hi : i = 0 ∨ i = 1 ∨ 2 ≤ i := by omega
    · rw [ha0]; exact Nat.zero_le _
    · have e := h.acc 1
      rw [sum_range_one, ha0, Nat.mul_zero, Nat.add_zero] at e
      have c : (lay N 1).card ≤ U.card := card_ones_le (F := N) fun C hC => hFU C (h.sub hC)
      calc a 1 ≤ (lay N 1).card := e
        _ ≤ 2 * n := c.trans hU
        _ ≤ β 1 * n := Nat.mul_le_mul_right _ hT.one
    have h2 : ∑ i' ∈ range i, 2 * θ (i - i') * a i' ≤ (∑ i' ∈ range i, 2 * θ (i - i') * β i') * n := by
      rw [sum_mul]
      refine sum_le_sum fun i' hi' => ?_
      have hlt := mem_range.1 hi'
      rw [Nat.mul_assoc (2 * θ (i - i'))]
      exact Nat.mul_le_mul_left _ (ih i' hlt (hlt.trans hik))
    calc a i ≤ (lay N i).card + ∑ i' ∈ range i, 2 * θ (i - i') * a i' := h.acc i
      _ ≤ 4 * θ (i - 1) * n + (∑ i' ∈ range i, 2 * θ (i - i') * β i') * n :=
        Nat.add_le_add (UniformInK.Bound.card_lay_le hU hFU h (by omega)) h2
      _ = (4 * θ (i - 1) + ∑ i' ∈ range i, 2 * θ (i - i') * β i') * n := by rw [Nat.add_mul]
      _ ≤ β i * n := Nat.mul_le_mul_right _ (hT.step i hi hik)
end SparsificationLemma.Bound

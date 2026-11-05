-- Prove2me | solution 1 for WidthK.Step.acc_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:16:52.019761+00:00
-- url     : https://prove2.me/submissions/ab8a0454-5bb8-4630-8222-271b6b7fc963

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_StepMachines_Math_Sparsify
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Definitions.Def_SparsifyWidthK_Step
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_Sparsify_mul_card_le
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open WidthK
open Finset Groundwork Groundwork.Sparsify
variable {α : Type*} [DecidableEq α]
open Step
variable {θ : ℕ → ℕ} {k j : ℕ} {F : Finset (Finset α)} {H : Finset α}
variable {τ p t : ℕ} {φ : Finset (Finset α)}
variable {n : ℕ} {U : Finset α} {β : ℕ → ℕ}
namespace WidthK
namespace Step
theorem _root_.solution {d : ℕ → ℕ} {N : Finset (Finset α)} {a : ℕ → ℕ} (hU : U.card ≤ 2 * n) (hFU : ∀ C ∈ F, C ⊆ U)
    (h : InvK d F N a) (ha0 : a 0 = 0) (hβ : ∀ i, 0 < i → d i * (2 + ∑ i' ∈ range i, β i') ≤ β i) (i : ℕ) :
    a i ≤ β i * n := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [ha0]; exact Nat.zero_le _
    have h1 : (lay N i).card ≤ 2 * n * d i := by
      have := mul_card_le U (lay N i) i (d i) (fun C hC => hFU C (h.sub (mem_filter.1 hC).1))
        (fun C hC => (mem_filter.1 hC).2) (h.deg i)
      calc (lay N i).card ≤ i * (lay N i).card := Nat.le_mul_of_pos_left _ hi
        _ ≤ U.card * d i := this
        _ ≤ 2 * n * d i := Nat.mul_le_mul_right _ hU
    have h2 : ∑ i' ∈ range i, a i' ≤ (∑ i' ∈ range i, β i') * n := by
      rw [sum_mul]
      exact sum_le_sum fun i' hi' => ih i' (mem_range.1 hi')
    calc a i ≤ (lay N i).card + d i * ∑ i' ∈ range i, a i' := h.acc i
      _ ≤ 2 * n * d i + d i * ((∑ i' ∈ range i, β i') * n) := Nat.add_le_add h1 (Nat.mul_le_mul_left _ h2)
      _ = d i * (2 + ∑ i' ∈ range i, β i') * n := by ring
      _ ≤ β i * n := Nat.mul_le_mul_right _ (hβ i hi)
end Step
end WidthK

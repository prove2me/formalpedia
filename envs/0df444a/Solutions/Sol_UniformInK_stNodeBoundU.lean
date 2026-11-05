-- Prove2me | solution 1 for UniformInK.stNodeBoundU
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T22:27:57.562681+00:00
-- url     : https://prove2.me/submissions/36a6cc93-475b-458c-9cde-8a11e6fdf6ce

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_StepMachines_Math_Sparsify
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_UniformInK_Spars_Bound
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all

set_option autoImplicit false
section
section
open UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK

namespace Groundwork.Sparsify

variable {α : Type*} [DecidableEq α]

/-- Double counting: `i`-subsets of `U`, each point in at most `d` of them. -/
theorem mul_card_le (U : Finset α) (G : Finset (Finset α)) (i d : ℕ)
    (hU : ∀ C ∈ G, C ⊆ U) (hi : ∀ C ∈ G, C.card = i)
    (hd : ∀ a, (G.filter fun C => a ∈ C).card ≤ d) : i * G.card ≤ U.card * d := by
  have := sum_card_inter_le (s := U) (B := G) (n := d) fun a _ => hd a
  rw [sum_congr rfl fun C hC => by rw [inter_eq_right.2 (hU C hC), hi C hC], sum_const] at this
  simpa [Nat.mul_comm] using this

end Groundwork.Sparsify

namespace UniformInK.Bound

variable {α : Type*} [DecidableEq α] {θ β : ℕ → ℕ} {k τ n : ℕ}
  {φ F N : Finset (Finset α)} {U : Finset α} {a : ℕ → ℕ} {p t : ℕ}

/-- At most `4 * θ (i - 1) * n` added clauses of positive size `i` remain. -/
theorem card_lay_le (hU : U.card ≤ 2 * n) (hFU : ∀ C ∈ F, C ⊆ U)
    (h : InvU θ F N a) {i : ℕ} (hi : 0 < i) :
    (lay N i).card ≤ 4 * θ (i - 1) * n := by
  have hd : ∀ y, ((lay N i).filter fun C => y ∈ C).card ≤ 2 * θ (i - 1) := by
    intro y
    have := h.deg i {y} (singleton_nonempty y) (by rw [card_singleton]; exact hi)
    simpa only [singleton_subset_iff, card_singleton] using this
  have := mul_card_le U (lay N i) i (2 * θ (i - 1))
    (fun C hC => hFU C (h.sub (mem_filter.1 hC).1))
    (fun C hC => (mem_filter.1 hC).2) hd
  calc
    (lay N i).card ≤ i * (lay N i).card := Nat.le_mul_of_pos_left _ hi
    _ ≤ U.card * (2 * θ (i - 1)) := this
    _ ≤ 2 * n * (2 * θ (i - 1)) := Nat.mul_le_mul_right _ hU
    _ = 4 * θ (i - 1) * n := by ring

/-- Strong induction bounds the number of added clauses of each size below `k`. -/
theorem acc_le (hT : ThrU k τ θ β) (hU : U.card ≤ 2 * n)
    (hFU : ∀ C ∈ F, C ⊆ U) (h : InvU θ F N a) (ha0 : a 0 = 0)
    (i : ℕ) (hik : i < k) : a i ≤ β i * n := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [ha0]
      exact Nat.zero_le _
    have h2 : ∑ i' ∈ range i, 2 * θ (i - i') * a i' ≤
        (∑ i' ∈ range i, 2 * θ (i - i') * β i') * n := by
      rw [sum_mul]
      refine sum_le_sum fun i' hi' => ?_
      have hlt := mem_range.1 hi'
      rw [Nat.mul_assoc (2 * θ (i - i'))]
      exact Nat.mul_le_mul_left _ (ih i' hlt (hlt.trans hik))
    calc
      a i ≤ (lay N i).card + ∑ i' ∈ range i, 2 * θ (i - i') * a i' := h.acc i
      _ ≤ 4 * θ (i - 1) * n + (∑ i' ∈ range i, 2 * θ (i - i') * β i') * n :=
        Nat.add_le_add (card_lay_le hU hFU h hi) h2
      _ = (4 * θ (i - 1) + ∑ i' ∈ range i, 2 * θ (i - i') * β i') * n := by
        rw [Nat.add_mul]
      _ ≤ β i * n := Nat.mul_le_mul_right _ (hT.step i hi hik)

/-- Every clause in a node is contained in the ambient vertex set. -/
theorem subset_of (hφ : ∀ C ∈ φ, C ⊆ U) (h : NodeU θ k τ φ F p t) :
    ∀ C ∈ F, C ⊆ U := by
  intro C hC
  obtain ⟨C', hC', hsub, -⟩ := h.1 C hC
  exact hsub.trans (hφ C' hC')

/-- The invariant and threshold recurrence imply both global path bounds. -/
theorem bound (hT : ThrU k τ θ β) (hU : U.card ≤ 2 * n)
    (hφ : ∀ C ∈ φ, C ⊆ U) (h : NodeU θ k τ φ F p t) :
    p ≤ (∑ i ∈ range k, β i) * n ∧ t ≤ k * n := by
  have hFU := subset_of hφ h
  obtain ⟨-, N, a, hh, hI, ha0, hh1, hp, ht⟩ := h
  have ha := acc_le hT hU hFU hI ha0
  constructor
  · rw [sum_mul]
    exact hp.trans (sum_le_sum fun i hi => ha i (mem_range.1 hi))
  · refine ht.trans ?_
    rw [mul_sum]
    refine (sum_le_card_nsmul _ _ n fun r hr => ?_).trans (by simp)
    have har := ha r (mem_range.1 hr)
    have h1 : τ * hh r * β r ≤ n * β r := by
      calc
        τ * hh r * β r = hh r * (τ * β r) := by ring
        _ ≤ hh r * θ r := Nat.mul_le_mul_left _ (hT.mul r)
        _ ≤ a r := hh1 r
        _ ≤ β r * n := har
        _ = n * β r := Nat.mul_comm _ _
    rcases Nat.eq_zero_or_pos (β r) with h0 | h0
    · have h2 := (hh1 r).trans har
      rw [h0, Nat.zero_mul] at h2
      have h3 : hh r = 0 := by
        rcases Nat.eq_zero_or_pos (hh r) with h | h
        · exact h
        · exact absurd (Nat.mul_pos h (hT.pos r)) (by omega)
      rw [h3, Nat.mul_zero]
      exact Nat.zero_le _
    · exact Nat.le_of_mul_le_mul_right h1 h0

end UniformInK.Bound

theorem solution : StNodeBoundU := by
  intro α _ θ β k τ n φ F U p t hT hU hφ h
  exact UniformInK.Bound.bound hT hU hφ h

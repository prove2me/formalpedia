-- Prove2me | solution 1 for Variance.stHence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:37:43.745625+00:00
-- url     : https://prove2.me/submissions/ba716c17-9129-43b0-b301-043895eb2cb2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Variance_Cov
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Variance_Var
import Theorems.Thm_Variance_stMeeting
import Theorems.Thm_Variance_sum_ordered_c


set_option autoImplicit false
section
section
open Variance
open Finset Eight.SecNetworks
namespace Variance
theorem _root_.solution : StHence := by
  intro g P c hs hP κ m hm h0 h1
  have hrow : ∀ p ∈ ordered g, ∑ q ∈ ordered g, ((c p.1 p.2 : ℕ) : ℤ) * ((c q.1 q.2 : ℕ) : ℤ) * κ p q ≤ ((c p.1 p.2 : ℕ) : ℤ) * (((4 * P : ℕ) : ℤ) * m) := by
    intro p hp
    have hsplit : ∑ q ∈ ordered g, ((c p.1 p.2 : ℕ) : ℤ) * ((c q.1 q.2 : ℕ) : ℤ) * κ p q = ∑ q ∈ ordered g with Meets p q, ((c p.1 p.2 : ℕ) : ℤ) * ((c q.1 q.2 : ℕ) : ℤ) * κ p q := by
      rw [sum_filter]
      refine sum_congr rfl fun q hq => ?_
      by_cases h : Meets p q
      · rw [if_pos h]
      · rw [if_neg h, h0 p hp q hq h, mul_zero]
    rw [hsplit]
    calc ∑ q ∈ ordered g with Meets p q, ((c p.1 p.2 : ℕ) : ℤ) * ((c q.1 q.2 : ℕ) : ℤ) * κ p q
        ≤ ∑ q ∈ ordered g with Meets p q, ((c p.1 p.2 : ℕ) : ℤ) * ((c q.1 q.2 : ℕ) : ℤ) * m :=
          sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (h1 p q) (by positivity)
      _ = ((c p.1 p.2 : ℕ) : ℤ) * (((∑ q ∈ ordered g with Meets p q, c q.1 q.2 : ℕ) : ℤ) * m) := by
          push_cast
          rw [sum_mul, mul_sum]
          exact sum_congr rfl fun q _ => by ring
      _ ≤ ((c p.1 p.2 : ℕ) : ℤ) * (((4 * P : ℕ) : ℤ) * m) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by exact_mod_cast stMeeting g P c hs hP p) hm) (by positivity)
  calc ∑ p ∈ ordered g, ∑ q ∈ ordered g, ((c p.1 p.2 : ℕ) : ℤ) * ((c q.1 q.2 : ℕ) : ℤ) * κ p q
      ≤ ∑ p ∈ ordered g, ((c p.1 p.2 : ℕ) : ℤ) * (((4 * P : ℕ) : ℤ) * m) := sum_le_sum hrow
    _ = ((4 * P * (∑ a, ∑ b ∈ univ.erase a, c a b) : ℕ) : ℤ) * m := by
        rw [← sum_ordered_c, ← sum_mul]
        push_cast
        ring
end Variance

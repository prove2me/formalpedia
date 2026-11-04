-- Prove2me | solution 1 for ThreeSum.Balancing.exists_balanced_offset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:16:43.203102+00:00
-- url     : https://prove2.me/submissions/02dff198-5fb9-4358-88c8-5602b2a77c0d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSum_Balancing
import Theorems.Thm_ThreeSum_Balancing_sum_correlation

set_option autoImplicit false
open ThreeSum ThreeSum.Balancing
open Finset
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] [Fintype G]
namespace ThreeSum.Balancing
theorem _root_.solution (F H : G → ℕ) :
    ∃ d, Fintype.card G * correlation F H d ≤ (∑ k, F k) * (∑ k, H k) := by
  by_contra! h
  have hs : (∑ _d : G, (∑ k, F k) * (∑ k, H k)) <
      ∑ d, Fintype.card G * correlation F H d := by
    exact sum_lt_sum_of_nonempty (by simp) (by simpa using h)
  simp only [sum_const, nsmul_eq_mul, card_univ, ← mul_sum, sum_correlation] at hs
  exact (lt_irrefl _ hs)
end ThreeSum.Balancing

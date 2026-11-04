-- Prove2me | solution 1 for ThreeSum.Arithmetic.weighted_indicator_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:13.517087+00:00
-- url     : https://prove2.me/submissions/e9567603-3ad5-431d-975a-98b204e2d6ce

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_WeightedCache3SUM_Alias_b1605bee33c94013
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_add_hits

set_option autoImplicit false
open ThreeSum ThreeSum.Arithmetic
open Finset
open scoped BigOperators
namespace ThreeSum.Arithmetic
theorem _root_.solution (L : Finset ℤ) (m x : ℤ)
    (hcop : ∀ l ∈ L, ∃ u v : ℤ, u * m + v * l = 1) :
    (if m ∣ x then missWeight L x else 0) +
        (∑ l ∈ L, dividesIndicator (m * l) x) =
      L.card * dividesIndicator m x := by
  by_cases hm : m ∣ x
  · have hsum : (∑ l ∈ L, dividesIndicator (m * l) x) =
        ∑ l ∈ L, dividesIndicator l x := by
      apply Finset.sum_congr rfl
      intro l hl
      simp [dividesIndicator, mul_dvd_iff_of_bezout (hcop l hl), hm]
    rw [if_pos hm, hsum]
    simpa [dividesIndicator, hm] using missWeight_add_hits L x
  · have hsum : (∑ l ∈ L, dividesIndicator (m * l) x) = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      have hnot : ¬ m * l ∣ x := fun h => hm ((mul_dvd_iff_of_bezout (hcop l hl)).mp h).1
      simp [dividesIndicator, hnot]
    rw [if_neg hm, hsum]
    simp [hm, dividesIndicator]
end ThreeSum.Arithmetic

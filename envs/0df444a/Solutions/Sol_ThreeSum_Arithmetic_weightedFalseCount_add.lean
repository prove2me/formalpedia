-- Prove2me | solution 1 for ThreeSum.Arithmetic.weightedFalseCount_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:07:07.553193+00:00
-- url     : https://prove2.me/submissions/f7c154d1-8031-42de-97a8-0994c8c2adbb

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Theorems.Thm_ThreeSum_Arithmetic_weighted_indicator_identity

set_option autoImplicit false
open ThreeSum ThreeSum.Arithmetic
open Finset
open scoped BigOperators
namespace ThreeSum.Arithmetic
theorem _root_.solution {ι : Type*} (T : Finset ι) (difference : ι → ℤ)
    (L : Finset ℤ) (m : ℤ)
    (hcop : ∀ l ∈ L, ∃ u v : ℤ, u * m + v * l = 1) :
    weightedFalseCount T difference L m +
        (∑ l ∈ L, modCount T difference (m * l)) =
      L.card * modCount T difference m := by
  unfold weightedFalseCount modCount
  calc
    (∑ i ∈ T, if m ∣ difference i then missWeight L (difference i) else 0) +
        (∑ l ∈ L, ∑ i ∈ T, dividesIndicator (m * l) (difference i)) =
      ∑ i ∈ T, ((if m ∣ difference i then missWeight L (difference i) else 0) +
        ∑ l ∈ L, dividesIndicator (m * l) (difference i)) := by
          rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ = ∑ i ∈ T, L.card * dividesIndicator m (difference i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact weighted_indicator_identity L m (difference i) hcop
    _ = L.card * (∑ i ∈ T, dividesIndicator m (difference i)) := by
      rw [Finset.mul_sum]
end ThreeSum.Arithmetic

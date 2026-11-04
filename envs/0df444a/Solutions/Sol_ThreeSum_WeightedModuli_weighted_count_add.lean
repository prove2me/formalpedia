-- Prove2me | solution 1 for ThreeSum.WeightedModuli.weighted_count_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:49:27.327851+00:00
-- url     : https://prove2.me/submissions/6bcb55bc-9625-4707-8d10-0fd96af7bd36

import Definitions.Def_Submission_ThreeSum_Auxiliary
import Definitions.Def_Submission_ThreeSum_WeightedModuli
import Theorems.Thm_ThreeSum_WeightedModuli_weighted_indicator

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedModuli
open Finset Arithmetic
open scoped BigOperators
namespace ThreeSum.WeightedModuli
theorem _root_.solution {ι : Type*} (T : Finset ι) (difference : ι → ℤ)
    (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p) (q : ℕ) :
    weightedFalseCount T difference (Auxiliary.moduli C) q +
      (∑ p ∈ C, modCount T difference (joint q p)) =
      C.card * modCount T difference q := by
  unfold weightedFalseCount modCount
  calc
    _ = ∑ i ∈ T, ((if (q : ℤ) ∣ difference i then
        missWeight (Auxiliary.moduli C) (difference i) else 0) +
        ∑ p ∈ C, dividesIndicator (joint q p) (difference i)) := by
          rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ = ∑ i ∈ T, C.card * dividesIndicator q (difference i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact weighted_indicator C hC q (difference i)
    _ = _ := by rw [Finset.mul_sum]
end ThreeSum.WeightedModuli

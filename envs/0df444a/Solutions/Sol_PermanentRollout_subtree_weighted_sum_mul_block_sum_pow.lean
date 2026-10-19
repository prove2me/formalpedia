-- Prove2me | solution 1 for PermanentRollout.subtree_weighted_sum_mul_block_sum_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/dd719885-3a2d-422b-b301-369f0245532c

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_subtree_single_surviving_block

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {R ι : Type*} [CommSemiring R] [DecidableEq ι]
    (s : Finset ι) (y a : ι → R) (t d : ℕ) (hd : d ≤ t)
    (hnil : ∀ j ∈ s, y j ^ (t + 1) = 0) :
    (∑ i ∈ s, a i *
      (y i ^ (t - d) * ∏ j ∈ s.erase i, y j ^ t)) *
        (∑ j ∈ s, y j) ^ d =
      (∑ i ∈ s, a i) * ∏ j ∈ s, y j ^ t := by
  calc
    (∑ i ∈ s, a i *
      (y i ^ (t - d) * ∏ j ∈ s.erase i, y j ^ t)) *
          (∑ j ∈ s, y j) ^ d =
        ∑ i ∈ s, a i *
          ((y i ^ (t - d) * ∏ j ∈ s.erase i, y j ^ t) *
            (∑ j ∈ s, y j) ^ d) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i _
              ring
    _ = ∑ i ∈ s, a i * (∏ j ∈ s, y j ^ t) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [subtree_single_surviving_block s y t d hi hd hnil]
    _ = (∑ i ∈ s, a i) * ∏ j ∈ s, y j ^ t := by
      rw [Finset.sum_mul]
end PermanentRollout

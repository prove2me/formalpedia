-- Prove2me | solution 1 for PermanentRollout.subtree_single_surviving_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/1ff3ff26-2b07-4dd1-89f8-d61116020439

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_subtreeTopProduct_mul_other_sum_eq_zero
import Theorems.Thm_PermanentRollout_subtree_mul_add_pow_eq_of_annihilates

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {R ι : Type*} [CommSemiring R] [DecidableEq ι]
    (s : Finset ι) (y : ι → R) (t d : ℕ) {i : ι}
    (hi : i ∈ s) (hd : d ≤ t)
    (hnil : ∀ j ∈ s, y j ^ (t + 1) = 0) :
    (y i ^ (t - d) * ∏ j ∈ s.erase i, y j ^ t) *
        (∑ j ∈ s, y j) ^ d =
      ∏ j ∈ s, y j ^ t := by
  have hother := subtreeTopProduct_mul_other_sum_eq_zero s y t i hnil
  have hsum : (∑ j ∈ s, y j) = y i + ∑ j ∈ s.erase i, y j :=
    (Finset.add_sum_erase s y hi).symm
  have hcut := subtree_mul_add_pow_eq_of_annihilates
    (∏ j ∈ s.erase i, y j ^ t) (y i)
    (∑ j ∈ s.erase i, y j) hother d
  have hdegree : t - d + d = t := Nat.sub_add_cancel hd
  calc
    (y i ^ (t - d) * ∏ j ∈ s.erase i, y j ^ t) *
          (∑ j ∈ s, y j) ^ d =
        y i ^ (t - d) *
          ((∏ j ∈ s.erase i, y j ^ t) *
            (y i + ∑ j ∈ s.erase i, y j) ^ d) := by
              rw [hsum]
              ring
    _ = y i ^ (t - d) *
          ((∏ j ∈ s.erase i, y j ^ t) * y i ^ d) := by rw [hcut]
    _ = (∏ j ∈ s.erase i, y j ^ t) *
          (y i ^ (t - d) * y i ^ d) := by ring
    _ = (∏ j ∈ s.erase i, y j ^ t) * y i ^ t := by
      rw [← pow_add, hdegree]
    _ = ∏ j ∈ s, y j ^ t :=
      Finset.prod_erase_mul s (fun j => y j ^ t) hi
end PermanentRollout

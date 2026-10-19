-- Prove2me | solution 1 for PermanentRollout.subtreeTopProduct_mul_other_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/31cde0cc-b3f6-4852-bcea-1ef2413c31c3

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_subtreeTopProduct_mul_mem_eq_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {R ι : Type*} [CommSemiring R] [DecidableEq ι]
    (s : Finset ι) (y : ι → R) (t : ℕ) (i : ι)
    (hnil : ∀ j ∈ s, y j ^ (t + 1) = 0) :
    (∏ j ∈ s.erase i, y j ^ t) *
        (∑ j ∈ s.erase i, y j) = 0 := by
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro j hj
  exact subtreeTopProduct_mul_mem_eq_zero (s.erase i) y t hj
    (hnil j (Finset.mem_of_mem_erase hj))
end PermanentRollout

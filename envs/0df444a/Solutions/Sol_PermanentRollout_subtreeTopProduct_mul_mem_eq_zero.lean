-- Prove2me | solution 1 for PermanentRollout.subtreeTopProduct_mul_mem_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/56be8ba8-036e-4c31-882d-f70d3bc43f81

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {R ι : Type*} [CommSemiring R] [DecidableEq ι]
    (s : Finset ι) (y : ι → R) (t : ℕ) {i : ι}
    (hi : i ∈ s) (hnil : y i ^ (t + 1) = 0) :
    (∏ j ∈ s, y j ^ t) * y i = 0 := by
  calc
    (∏ j ∈ s, y j ^ t) * y i =
        (∏ j ∈ s.erase i, y j ^ t) * (y i ^ t * y i) := by
          rw [← Finset.prod_erase_mul s (fun j => y j ^ t) hi]
          ring
    _ = 0 := by rw [← pow_succ, hnil, mul_zero]
end PermanentRollout

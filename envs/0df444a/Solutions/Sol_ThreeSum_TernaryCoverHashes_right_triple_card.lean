-- Prove2me | solution 1 for ThreeSum.TernaryCoverHashes.right_triple_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:07:10.807079+00:00
-- url     : https://prove2.me/submissions/951b738e-3906-47b5-94c0-315fe2f682cf

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
import Theorems.Thm_ThreeSum_TernaryCoverHashes_right_same_side_independent
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_HashFamily_hash_fiber_card
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverHashes
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [Field K]
variable [Fintype K] [DecidableEq K] [DecidableEq ι]
namespace ThreeSum.TernaryCoverHashes
theorem _root_.solution (x : ι → K) {y v : ι → K} (hyv : y ≠ v) (a b c : K) :
    Fintype.card K ^ 3 *
      ((pairEvent x y a b).filter fun w => linearHash (rightVector v) w = c).card =
        Fintype.card (Coordinate ι → K) := by
  classical
  have heq : ((pairEvent x y a b).filter fun w => linearHash (rightVector v) w = c) =
      Finset.univ.filter (fun w =>
        HashFamily.hashMap ![rightVector y, rightVector v, leftVector x] w = ![b, c, a]) := by
    ext w
    simp only [pairEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [funext_iff]
    simp [linearHash, HashFamily.hashMap_apply, Fin.forall_fin_succ, and_assoc, and_left_comm,
      and_comm]
  rw [heq]
  simpa using HashFamily.hash_fiber_card (right_same_side_independent hyv x) ![b, c, a]
end ThreeSum.TernaryCoverHashes

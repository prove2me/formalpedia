-- Prove2me | solution 1 for ThreeSum.TernaryCoverHashes.left_triple_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:07:09.756208+00:00
-- url     : https://prove2.me/submissions/6cb3ad9c-9eff-4b6b-8c92-13fb6a0a4387

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
import Theorems.Thm_ThreeSum_TernaryCoverHashes_same_side_independent
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_HashFamily_hash_fiber_card
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverHashes
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [Field K]
variable [Fintype K] [DecidableEq K] [DecidableEq ι]
namespace ThreeSum.TernaryCoverHashes
theorem _root_.solution {x u : ι → K} (hxu : x ≠ u) (y : ι → K) (a b c : K) :
    Fintype.card K ^ 3 *
      ((pairEvent x y a b).filter fun w => linearHash (leftVector u) w = c).card =
        Fintype.card (Coordinate ι → K) := by
  classical
  have heq : ((pairEvent x y a b).filter fun w => linearHash (leftVector u) w = c) =
      Finset.univ.filter (fun w =>
        HashFamily.hashMap ![leftVector x, leftVector u, rightVector y] w = ![a, c, b]) := by
    ext w
    simp only [pairEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [funext_iff]
    simp [linearHash, HashFamily.hashMap_apply, Fin.forall_fin_succ, and_assoc, and_left_comm,
      and_comm]
  rw [heq]
  simpa using HashFamily.hash_fiber_card (same_side_independent hxu y) ![a, c, b]
end ThreeSum.TernaryCoverHashes

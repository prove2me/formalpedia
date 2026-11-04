-- Prove2me | solution 1 for ThreeSum.TernaryCoverHashes.pairEvent_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:16:43.385031+00:00
-- url     : https://prove2.me/submissions/d3bd20a0-fd68-435f-a68d-79becaf2bcb9

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
import Theorems.Thm_ThreeSum_TernaryCoverHashes_pair_independent
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_HashFamily_hash_fiber_card
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverHashes
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [Field K]
variable [Fintype K] [DecidableEq K] [DecidableEq ι]
namespace ThreeSum.TernaryCoverHashes
theorem _root_.solution (x y : ι → K) (a b : K) :
    Fintype.card K ^ 2 * (pairEvent x y a b).card =
      Fintype.card (Coordinate ι → K) := by
  classical
  have heq : pairEvent x y a b = Finset.univ.filter (fun w =>
      HashFamily.hashMap ![leftVector x, rightVector y] w = ![a, b]) := by
    ext w
    simp only [pairEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [funext_iff]
    simp [linearHash, HashFamily.hashMap_apply, Fin.forall_fin_succ]
  rw [heq]
  simpa using HashFamily.hash_fiber_card (pair_independent x y) ![a, b]
end ThreeSum.TernaryCoverHashes

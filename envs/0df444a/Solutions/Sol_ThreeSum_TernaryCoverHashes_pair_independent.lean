-- Prove2me | solution 1 for ThreeSum.TernaryCoverHashes.pair_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:44:57.966039+00:00
-- url     : https://prove2.me/submissions/71085443-70c3-41d7-a811-96f4eb348e98

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
import Theorems.Thm_ThreeSum_TernaryCoverHashes_pair_relation
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverHashes
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [Field K]
namespace ThreeSum.TernaryCoverHashes
theorem _root_.solution (x y : ι → K) :
    LinearIndependent K ![leftVector x, rightVector y] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hr := pair_relation x y (a := g 0) (b := g 1) (fun p => by
    have hp := congrFun hg p
    simpa [Fin.sum_univ_succ] using hp)
  fin_cases i <;> simp_all
end ThreeSum.TernaryCoverHashes

-- Prove2me | solution 1 for ThreeSum.TernaryCoverHashes.right_same_side_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:45:33.034882+00:00
-- url     : https://prove2.me/submissions/1c88f2bb-2dcf-4138-81fa-719dc1ddd31d

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
import Theorems.Thm_ThreeSum_TernaryCoverHashes_right_same_side_relation
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverHashes
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [Field K]
namespace ThreeSum.TernaryCoverHashes
theorem _root_.solution {x y : ι → K} (hxy : x ≠ y) (z : ι → K) :
    LinearIndependent K ![rightVector x, rightVector y, leftVector z] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hr := right_same_side_relation hxy z (a := g 0) (b := g 1) (c := g 2)
    (fun p => by
      have hp := congrFun hg p
      simpa [Fin.sum_univ_succ, add_assoc] using hp)
  fin_cases i <;> simp_all
end ThreeSum.TernaryCoverHashes

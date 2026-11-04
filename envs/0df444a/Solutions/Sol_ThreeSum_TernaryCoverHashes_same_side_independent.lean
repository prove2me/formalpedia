-- Prove2me | solution 1 for ThreeSum.TernaryCoverHashes.same_side_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:44:59.05592+00:00
-- url     : https://prove2.me/submissions/d21a568a-16c9-4d96-8b33-27784521ac75

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
import Theorems.Thm_ThreeSum_TernaryCoverHashes_same_side_relation
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverHashes
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [Field K]
namespace ThreeSum.TernaryCoverHashes
theorem _root_.solution {x y : ι → K} (hxy : x ≠ y) (z : ι → K) :
    LinearIndependent K ![leftVector x, leftVector y, rightVector z] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hr := same_side_relation hxy z (a := g 0) (b := g 1) (c := g 2)
    (fun p => by
      have hp := congrFun hg p
      simpa [Fin.sum_univ_succ, add_assoc] using hp)
  fin_cases i <;> simp_all
end ThreeSum.TernaryCoverHashes

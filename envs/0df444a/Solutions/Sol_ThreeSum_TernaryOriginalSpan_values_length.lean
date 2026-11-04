-- Prove2me | solution 1 for ThreeSum.TernaryOriginalSpan.values_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:13:03.348209+00:00
-- url     : https://prove2.me/submissions/6b6c9eac-866d-4d46-b12d-5491ac484734

import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpan
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryOriginalSpan
variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V]
namespace ThreeSum.TernaryOriginalSpan
theorem _root_.solution (rows : List V) : (values K rows).length = Fintype.card K^rows.length := by
  induction rows with
  | nil => simp [values]
  | cons row rows ih =>
    simp only [values,List.length_flatMap,List.length_map,ih,List.length_cons]
    simp [pow_succ,Nat.mul_comm]
end ThreeSum.TernaryOriginalSpan

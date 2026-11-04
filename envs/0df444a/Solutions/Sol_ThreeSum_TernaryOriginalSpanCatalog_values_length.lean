-- Prove2me | solution 1 for ThreeSum.TernaryOriginalSpanCatalog.values_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:19:49.045027+00:00
-- url     : https://prove2.me/submissions/d39785b8-122b-449f-a5c0-c786314d8ce4

import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpan
import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpanCatalog
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryOriginalSpanCatalog
open Finset
set_option maxHeartbeats 2000000
variable {p J : ℕ}
namespace ThreeSum.TernaryOriginalSpanCatalog
theorem _root_.solution (rows : List (Fin J → ZMod p)) : (values p rows).length=p^rows.length := by
  induction rows with
  | nil => simp [values]
  | cons row rows ih =>
    simp only [values,List.length_flatMap,List.length_map,ih,List.length_cons]
    simp [pow_succ,Nat.mul_comm]
end ThreeSum.TernaryOriginalSpanCatalog

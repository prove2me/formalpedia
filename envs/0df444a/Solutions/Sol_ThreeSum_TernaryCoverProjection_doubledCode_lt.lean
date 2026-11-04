-- Prove2me | solution 1 for ThreeSum.TernaryCoverProjection.doubledCode_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:54:51.186916+00:00
-- url     : https://prove2.me/submissions/3f3b8aff-041e-4484-b34f-29f590453f66

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Definitions.Def_Submission_ThreeSum_TernaryCoverProjection
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverProjection
open Finset TernaryJointType TernaryCoverLocal
namespace ThreeSum.TernaryCoverProjection
theorem _root_.solution (swap : Bool) (a b : Fin 3) (hab : a.val + b.val ≤ 2) :
    doubledCode swap a b < 5 := by
  cases swap <;> simp only [doubledCode, Bool.false_eq_true, ite_false, ite_true] <;> omega
end ThreeSum.TernaryCoverProjection

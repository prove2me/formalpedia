-- Prove2me | solution 1 for ThreeSum.TernaryCoverProjection.differenceCode_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:54:05.938391+00:00
-- url     : https://prove2.me/submissions/b2dda929-a6d3-4ae5-aa1d-00d02dfda410

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Definitions.Def_Submission_ThreeSum_TernaryCoverProjection

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverProjection
open Finset TernaryJointType TernaryCoverLocal
namespace ThreeSum.TernaryCoverProjection
theorem _root_.solution (p : ℕ) (a b : Fin 3) :
    (differenceCode a b : ZMod p) = (a.val : ZMod p) - (b.val : ZMod p) + 2 := by
  have hb : b.val ≤ 2 := by have h := b.isLt; omega
  unfold differenceCode
  rw [Nat.cast_add, Nat.cast_sub hb]
  norm_num
  ring
end ThreeSum.TernaryCoverProjection

-- Prove2me | solution 1 for ThreeSum.TernaryCoverProjection.marked_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:54:08.454201+00:00
-- url     : https://prove2.me/submissions/b11a668c-ddf5-42c7-a61a-8a0cafeea7fc

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Definitions.Def_Submission_ThreeSum_TernaryCoverProjection
import Theorems.Thm_ThreeSum_TernaryCoverLocal_edge_data
import Theorems.Thm_ThreeSum_TernaryJointType_edge_joint_type


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverProjection
open Finset TernaryJointType TernaryCoverLocal
namespace ThreeSum.TernaryCoverProjection
theorem _root_.solution {L : ℕ} {α π : DigitType} (e : LocalEdge L α π)
    (hthirds : π 2 = 3 * α 2) :
    (marked e).card = π 2 / 3 := by
  have hcount := (edge_joint_type (edge_data e) hthirds).2.2.2.2.1
  have he : (marked e).card = jointCount (left e) (right e) 1 1 := by
    unfold marked
    rw [card_eq_sum_ones, sum_filter]
    rfl
  exact he.trans hcount
end ThreeSum.TernaryCoverProjection

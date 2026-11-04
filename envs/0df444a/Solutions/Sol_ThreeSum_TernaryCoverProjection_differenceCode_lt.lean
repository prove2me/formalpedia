-- Prove2me | solution 1 for ThreeSum.TernaryCoverProjection.differenceCode_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:53:15.533143+00:00
-- url     : https://prove2.me/submissions/b2815936-5167-4174-a7e5-89ec99574ea0

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Definitions.Def_Submission_ThreeSum_TernaryCoverProjection

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverProjection
open Finset TernaryJointType TernaryCoverLocal
namespace ThreeSum.TernaryCoverProjection
theorem _root_.solution (a b : Fin 3) : differenceCode a b < 5 := by
  have ha := a.isLt
  unfold differenceCode
  omega
end ThreeSum.TernaryCoverProjection

-- Prove2me | solution 1 for ThreeSum.TernaryWantedBatchIndex.cells_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:24:32.66502+00:00
-- url     : https://prove2.me/submissions/eed393eb-2d8a-4254-a3d8-d2c7aa4b3b9e

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchIndex
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWantedBatchIndex
open Light TernaryWantedLittleEndian
namespace ThreeSum.TernaryWantedBatchIndex
theorem _root_.solution (xs ys : List Entry) : cells (xs ++ ys) = cells xs ++ cells ys :=
  List.flatMap_append ..
end ThreeSum.TernaryWantedBatchIndex

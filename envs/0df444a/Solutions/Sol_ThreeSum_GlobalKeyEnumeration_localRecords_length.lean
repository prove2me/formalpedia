-- Prove2me | solution 1 for ThreeSum.GlobalKeyEnumeration.localRecords_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:17:15.396224+00:00
-- url     : https://prove2.me/submissions/3c190407-ef36-4e9b-b2d4-cc4d4da8a06f

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Theorems.Thm_ThreeSum_GlobalKeyEnumeration_layers_length

set_option autoImplicit false
open ThreeSum ThreeSum.GlobalKeyEnumeration
open GlobalEncoding LocalGraph LocalCoverBounds LocalHashMoments
open RadixKeyLists
open scoped BigOperators
set_option maxHeartbeats 1800000
namespace ThreeSum.GlobalKeyEnumeration
theorem _root_.solution (h : ℕ) :
    (localRecords h).length=scheduleSize h*outputCount (512*h) h := by
  calc
    _ = (List.finRange (scheduleSize h)).length*(layers h).length :=
      List.length_product _ _
    _ = _ := by rw [List.length_finRange,layers_length]
end ThreeSum.GlobalKeyEnumeration

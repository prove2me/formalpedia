-- Prove2me | solution 1 for ThreeSum.RawAKeyLists.records_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:55:47.292469+00:00
-- url     : https://prove2.me/submissions/af1d103c-9d16-4fd3-b926-c5f873b4e512

import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_RawAKeyLists

set_option autoImplicit false
open ThreeSum ThreeSum.RawAKeyLists
open GlobalEncoding RawIncidences GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open scoped BigOperators
set_option maxHeartbeats 900000
namespace ThreeSum.RawAKeyLists
theorem _root_.solution (xs : List ℤ) : (records xs).length=3*xs.length := by
  calc
    _ = (List.finRange 3).length*(List.finRange xs.length).length := List.length_product _ _
    _ = _ := by rw [List.length_finRange,List.length_finRange]
end ThreeSum.RawAKeyLists

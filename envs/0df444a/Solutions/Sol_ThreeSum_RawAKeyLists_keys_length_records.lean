-- Prove2me | solution 1 for ThreeSum.RawAKeyLists.keys_length_records
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:01:20.095874+00:00
-- url     : https://prove2.me/submissions/1414eed1-1f96-433e-bba8-41f65ed1eb3e

import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_RawAKeyLists

set_option autoImplicit false
open ThreeSum ThreeSum.RawAKeyLists
open GlobalEncoding RawIncidences GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open scoped BigOperators
set_option maxHeartbeats 900000
namespace ThreeSum.RawAKeyLists
theorem _root_.solution (P : ℤ) (xs : List ℤ) :
    (keys P xs).length=(records xs).length := List.length_map ..
end ThreeSum.RawAKeyLists

-- Prove2me | solution 1 for ThreeSum.RawAKeyLists.selected_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:00:32.9302+00:00
-- url     : https://prove2.me/submissions/ae30b8a0-896f-40f5-981f-1e21a6baeb77

import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Theorems.Thm_ThreeSum_GlobalKeyOffset_selected_lt
import Theorems.Thm_ThreeSum_LightOriginalOffset_selected_lt


set_option autoImplicit false
open ThreeSum ThreeSum.RawAKeyLists
open GlobalEncoding RawIncidences GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open scoped BigOperators
set_option maxHeartbeats 900000
namespace ThreeSum.RawAKeyLists
theorem _root_.solution (M : ℕ) [NeZero M] (P : ℤ) (xs : List ℤ) (h J : ℕ) :
    selected M P xs h J < M := GlobalKeyOffset.selected_lt ..
end ThreeSum.RawAKeyLists

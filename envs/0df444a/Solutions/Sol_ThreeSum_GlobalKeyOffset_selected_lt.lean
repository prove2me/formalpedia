-- Prove2me | solution 1 for ThreeSum.GlobalKeyOffset.selected_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:51:54.970237+00:00
-- url     : https://prove2.me/submissions/a909c60c-2c2e-4e54-87c4-4597fabdf3a3

import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Definitions.Def_Submission_ThreeSum_LightOriginalOffset
import Definitions.Def_Submission_ThreeSum_RawReporting
import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
import Theorems.Thm_ThreeSum_LightOriginalOffset_selected_lt


set_option autoImplicit false
open ThreeSum ThreeSum.GlobalKeyOffset
open GlobalEncoding GlobalKeyEnumeration
open scoped BigOperators
set_option maxHeartbeats 1800000
namespace ThreeSum.GlobalKeyOffset
theorem _root_.solution (p : ℕ) [NeZero p] (left : List ℤ) (h J : ℕ) :
    selected p left h J < p := LightOriginalOffset.selected_lt ..
end ThreeSum.GlobalKeyOffset

-- Prove2me | solution 1 for ThreeSum.ReportingHostSuffix.liftSet_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:21:32.169007+00:00
-- url     : https://prove2.me/submissions/60fcabf5-3039-4e10-b2de-5f2b7ed739b8

import Definitions.Def_Submission_ThreeSum_LightBlockBoxes
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffix
open Finset ThreeSum.SubsetAddress BlockIndexedQuery BlockRows BlockIndex BlockForced
open GlobalEncoding LocalCoverBounds StoredReporting LightBlockQuery
open scoped BigOperators
namespace ThreeSum.ReportingHostSuffix
theorem _root_.solution {W V offset : ℕ} (hfit : offset+V ≤ W) (S : Finset (Fin V)) :
    (liftSet hfit S).card = S.card := Finset.card_map _
end ThreeSum.ReportingHostSuffix

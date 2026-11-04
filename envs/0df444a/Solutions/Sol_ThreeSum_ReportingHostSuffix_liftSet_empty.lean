-- Prove2me | solution 1 for ThreeSum.ReportingHostSuffix.liftSet_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:21:34.634204+00:00
-- url     : https://prove2.me/submissions/97ed1e4a-b458-4f54-9254-2763efd8ba69

import Definitions.Def_Submission_ThreeSum_LightBlockBoxes
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffix
open Finset ThreeSum.SubsetAddress BlockIndexedQuery BlockRows BlockIndex BlockForced
open GlobalEncoding LocalCoverBounds StoredReporting LightBlockQuery
open scoped BigOperators
namespace ThreeSum.ReportingHostSuffix
theorem _root_.solution {W V offset : ℕ} (hfit : offset+V ≤ W) :
    liftSet hfit ∅ = ∅ := Finset.map_empty _
end ThreeSum.ReportingHostSuffix

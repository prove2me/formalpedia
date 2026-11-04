-- Prove2me | solution 1 for ThreeSum.ReportingHostSuffix.liftSet_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:49:55.583239+00:00
-- url     : https://prove2.me/submissions/7b4ffed8-1e1a-48fc-a60c-01f0a42da837

import Definitions.Def_Submission_ThreeSum_LightBlockBoxes
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffix
open Finset ThreeSum.SubsetAddress BlockIndexedQuery BlockRows BlockIndex BlockForced
open GlobalEncoding LocalCoverBounds StoredReporting LightBlockQuery
open scoped BigOperators
namespace ThreeSum.ReportingHostSuffix
theorem _root_.solution {W V offset : ℕ} (hfit : offset+V ≤ W) :
    Function.Injective (liftSet hfit) := Finset.map_injective _
end ThreeSum.ReportingHostSuffix

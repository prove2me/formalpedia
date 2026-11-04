-- Prove2me | solution 1 for ThreeSum.ReportingHostSuffix.liftSet_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:23:03.283689+00:00
-- url     : https://prove2.me/submissions/06210d3c-9633-4eb3-860c-34ade36f4868

import Definitions.Def_Submission_ThreeSum_LightBlockBoxes
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffix
open Finset ThreeSum.SubsetAddress BlockIndexedQuery BlockRows BlockIndex BlockForced
open GlobalEncoding LocalCoverBounds StoredReporting LightBlockQuery
open scoped BigOperators
namespace ThreeSum.ReportingHostSuffix
theorem _root_.solution {W V offset : ℕ} (hfit : offset+V ≤ W) (S T : Finset (Fin V)) :
    liftSet hfit S ⊆ liftSet hfit T ↔ S ⊆ T := Finset.map_subset_map
end ThreeSum.ReportingHostSuffix

-- Prove2me | solution 1 for ThreeSum.ReportingHostSuffix.lift_localQuery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:41:25.036676+00:00
-- url     : https://prove2.me/submissions/03e868e9-33b5-4e6a-ab00-9a9521b151b5

import Definitions.Def_Submission_ThreeSum_LightBlockBoxes
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix
import Theorems.Thm_ThreeSum_ReportingHostSuffix_lift_lowerSet
import Theorems.Thm_ThreeSum_ReportingHostSuffix_block_query_in_range

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffix
open Finset ThreeSum.SubsetAddress BlockIndexedQuery BlockRows BlockIndex BlockForced
open GlobalEncoding LocalCoverBounds StoredReporting LightBlockQuery
open scoped BigOperators
namespace ThreeSum.ReportingHostSuffix
theorem _root_.solution {J L k : ℕ} (hk : k ≤ J) (Q : Fin J → Finset (Fin L)) :
    liftSet (block_fit hk) (localQuery hk Q) = querySet k Q :=
  lift_lowerSet (block_fit hk) _ (block_query_in_range hk Q)
end ThreeSum.ReportingHostSuffix

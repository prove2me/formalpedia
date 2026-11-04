-- Prove2me | solution 1 for ThreeSum.ReportingHostSuffix.shiftEmbedding_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:21:33.391939+00:00
-- url     : https://prove2.me/submissions/7c3150ed-2577-4c53-b4fc-ff99cfd8f366

import Definitions.Def_Submission_ThreeSum_LightBlockBoxes
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffix
open Finset ThreeSum.SubsetAddress BlockIndexedQuery BlockRows BlockIndex BlockForced
open GlobalEncoding LocalCoverBounds StoredReporting LightBlockQuery
open scoped BigOperators
namespace ThreeSum.ReportingHostSuffix
theorem _root_.solution {W V offset : ℕ} (hfit : offset+V ≤ W) (i : Fin V) :
    (shiftEmbedding offset hfit i).val = offset+i.val := rfl
end ThreeSum.ReportingHostSuffix

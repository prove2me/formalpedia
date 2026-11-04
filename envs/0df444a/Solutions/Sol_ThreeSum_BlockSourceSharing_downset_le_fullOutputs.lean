-- Prove2me | solution 1 for ThreeSum.BlockSourceSharing.downset_le_fullOutputs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:48:14.683916+00:00
-- url     : https://prove2.me/submissions/fbd7c154-4019-453c-856f-f56a7e0284ce

import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightSourceGather
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixCosts
import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSum_BlockSourceSharing
import Theorems.Thm_ThreeSum_ReportingHostSuffixCosts_downsetCap_le_layer


set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceSharing
open BlockEncoding GlobalEncoding BlockIndexedQuery SubsetAddress
open Scales TrimScales CostLedger StageBounds
namespace ThreeSum.BlockSourceSharing
theorem _root_.solution (n : ℕ) :
    downsetCap (256*mu n) (mu n) ≤ (mu n+1)*fullOutputs n :=
  ReportingHostSuffixCosts.downsetCap_le_layer (by omega)
end ThreeSum.BlockSourceSharing

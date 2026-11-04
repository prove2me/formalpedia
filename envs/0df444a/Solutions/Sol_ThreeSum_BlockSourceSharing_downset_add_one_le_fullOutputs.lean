-- Prove2me | solution 1 for ThreeSum.BlockSourceSharing.downset_add_one_le_fullOutputs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:52:27.54925+00:00
-- url     : https://prove2.me/submissions/3a476a2c-7367-416c-89ad-3da9ac887445

import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightSourceGather
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixCosts
import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSum_BlockSourceSharing
import Theorems.Thm_ThreeSum_ReportingHostSuffixCosts_downsetCap_add_one_le_layer


set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceSharing
open BlockEncoding GlobalEncoding BlockIndexedQuery SubsetAddress
open Scales TrimScales CostLedger StageBounds
namespace ThreeSum.BlockSourceSharing
theorem _root_.solution (n : ℕ) :
    downsetCap (256*mu n) (mu n)+1 ≤ (256*mu n+2)*fullOutputs n :=
  ReportingHostSuffixCosts.downsetCap_add_one_le_layer (by omega)
end ThreeSum.BlockSourceSharing

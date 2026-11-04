-- Prove2me | solution 1 for ThreeSum.ReportingHostCatalogCosts.actual_catalog_time_le_prefixBoxes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:34:21.499835+00:00
-- url     : https://prove2.me/submissions/16a54633-43e2-49b3-9b3a-26e18c3385f2

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCatalogSetup
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixCosts
import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogCosts
import Theorems.Thm_ThreeSum_ReportingHostCatalogCosts_catalog_time_le_prefixBoxes

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostCatalogCosts
set_option maxRecDepth 8000
open ThreeSum.SubsetAddress ThreeSum.LightBlockQuery ThreeSum.BlockIndexedQuery
open ReportingHostPrefixCatalog ReportingHostSuffixCosts
namespace ThreeSum.ReportingHostCatalogCosts
theorem _root_.solution {n k : ℕ}
    (hk : k ≤ Scales.blockCount (Scales.inputBits n)) :
    LightReportingSuffixCatalogSetup.time
      (width (Scales.microHalf (Scales.inputBits n)) (Scales.blockCount (Scales.inputBits n)))
      (suffixStage (Scales.blockCount (Scales.inputBits n))
        (512*Scales.microHalf (Scales.inputBits n)) k)
      (Switch.residualSize n k-Switch.actualSwitch n k)
      (k*(512*Scales.microHalf (Scales.inputBits n)))
      (Fintype.card (Prefix (Scales.microHalf (Scales.inputBits n)) k)) ≤
      100000*(width (Scales.microHalf (Scales.inputBits n)) (Scales.blockCount (Scales.inputBits n))+1)^5*
        CostLedger.prefixBoxes n k :=
  catalog_time_le_prefixBoxes rfl rfl hk
end ThreeSum.ReportingHostCatalogCosts

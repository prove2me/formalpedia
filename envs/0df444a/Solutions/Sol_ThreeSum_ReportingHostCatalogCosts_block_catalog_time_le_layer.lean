-- Prove2me | solution 1 for ThreeSum.ReportingHostCatalogCosts.block_catalog_time_le_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:15:12.183336+00:00
-- url     : https://prove2.me/submissions/05e7601c-2afc-4538-b6c1-1ef1ab72035e

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCatalogSetup
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixCosts
import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogCosts
import Theorems.Thm_ThreeSum_ReportingHostCatalogCosts_prefix_card_pos
import Theorems.Thm_ThreeSum_ReportingHostCatalogCosts_catalog_time_le_layer
import Theorems.Thm_ThreeSum_ReportingHostPrefixCatalog_prefix_card
import Theorems.Thm_ThreeSum_ReportingHostSuffixCosts_suffix_width_eq


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostCatalogCosts
set_option maxRecDepth 8000
open ThreeSum.SubsetAddress ThreeSum.LightBlockQuery ThreeSum.BlockIndexedQuery
open ReportingHostPrefixCatalog ReportingHostSuffixCosts
namespace ThreeSum.ReportingHostCatalogCosts
theorem _root_.solution {h J k cut : ℕ} (hk : k ≤ J)
    (hcut : cut ≤ residualSize h J k) :
    LightReportingSuffixCatalogSetup.time (width h J) (suffixStage J (512*h) k) cut (k*(512*h))
      (Fintype.card (Prefix h k)) ≤
      100000*(width h J+1)^5*(((512*h).choose (2*h)*(2*h).choose h)^k)*
        (256*residualSize h J k).choose cut := by
  have hhalf : cut ≤ suffixStage J (512*h) k/2 := by
    rw [suffix_width_eq]
    omega
  calc
    _ ≤ 100000*(width h J+1)^5*(Fintype.card (Prefix h k))*
        (suffixStage J (512*h) k).choose cut :=
      catalog_time_le_layer (W := width h J) (V := suffixStage J (512*h) k)
        (offset := k*(512*h)) (ReportingHostSuffix.block_fit hk) hhalf (prefix_card_pos h k)
    _ = _ := by rw [prefix_card,suffix_width_eq]
end ThreeSum.ReportingHostCatalogCosts

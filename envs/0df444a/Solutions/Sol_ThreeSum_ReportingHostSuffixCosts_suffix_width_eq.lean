-- Prove2me | solution 1 for ThreeSum.ReportingHostSuffixCosts.suffix_width_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:38:56.776213+00:00
-- url     : https://prove2.me/submissions/e7b680e2-44d6-48bd-a024-a6d62e8b85f1

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSetup
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixCosts

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffixCosts
open ThreeSum.SubsetAddress ThreeSum.LightBlockQuery ThreeSum.BlockIndexedQuery
open scoped BigOperators
namespace ThreeSum.ReportingHostSuffixCosts
theorem _root_.solution (h J k : ℕ) :
    suffixStage J (512*h) k = 256*residualSize h J k := by
  unfold suffixStage residualSize
  ring
end ThreeSum.ReportingHostSuffixCosts

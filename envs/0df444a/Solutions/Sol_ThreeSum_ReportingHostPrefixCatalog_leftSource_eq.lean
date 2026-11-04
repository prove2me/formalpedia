-- Prove2me | solution 1 for ThreeSum.ReportingHostPrefixCatalog.leftSource_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:42:24.664737+00:00
-- url     : https://prove2.me/submissions/41c3075f-e933-4833-91a7-7469a5f70b66

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixBoxes
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixCatalog
open Finset LocalGraph LayerCounts BlockRows BlockIndex BlockIndexedQuery
open BlockEncoding BlockForced GlobalEncoding StoredReporting ReportingHostSuffix
set_option linter.unusedSectionVars false
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.ReportingHostPrefixCatalog
theorem _root_.solution {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ) (q : GlobalOutput h J) :
    leftSource P B b q = leftSourceOf (outputOccurrences q) P B b := rfl
end ThreeSum.ReportingHostPrefixCatalog

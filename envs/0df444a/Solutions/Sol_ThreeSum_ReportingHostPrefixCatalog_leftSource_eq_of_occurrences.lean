-- Prove2me | solution 1 for ThreeSum.ReportingHostPrefixCatalog.leftSource_eq_of_occurrences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:46:18.362417+00:00
-- url     : https://prove2.me/submissions/266aa57d-66b6-440c-9871-2bafed39a126

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixBoxes
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
import Theorems.Thm_ThreeSum_ReportingHostPrefixCatalog_leftSource_eq

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixCatalog
open Finset LocalGraph LayerCounts BlockRows BlockIndex BlockIndexedQuery
open BlockEncoding BlockForced GlobalEncoding StoredReporting ReportingHostSuffix
set_option linter.unusedSectionVars false
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.ReportingHostPrefixCatalog
theorem _root_.solution {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ)
    {q q' : GlobalOutput h J} (ho : outputOccurrences q = outputOccurrences q') :
    leftSource P B b q = leftSource P B b q' := by rw [leftSource_eq,leftSource_eq,ho]
end ThreeSum.ReportingHostPrefixCatalog

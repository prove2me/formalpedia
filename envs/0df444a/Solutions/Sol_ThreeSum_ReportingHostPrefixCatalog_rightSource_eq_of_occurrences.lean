-- Prove2me | solution 1 for ThreeSum.ReportingHostPrefixCatalog.rightSource_eq_of_occurrences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:47:01.649458+00:00
-- url     : https://prove2.me/submissions/d95f903b-4fd1-480b-9f2c-f3fae83ed305

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixBoxes
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
import Theorems.Thm_ThreeSum_ReportingHostPrefixCatalog_rightSource_eq

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixCatalog
open Finset LocalGraph LayerCounts BlockRows BlockIndex BlockIndexedQuery
open BlockEncoding BlockForced GlobalEncoding StoredReporting ReportingHostSuffix
set_option linter.unusedSectionVars false
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.ReportingHostPrefixCatalog
theorem _root_.solution {h J : ℕ} (P shift : ℤ) (C : Finset γ) (c : γ → ℤ)
    {q q' : GlobalOutput h J} (ho : outputOccurrences q = outputOccurrences q') :
    rightSource P shift C c q = rightSource P shift C c q' := by rw [rightSource_eq,rightSource_eq,ho]
end ThreeSum.ReportingHostPrefixCatalog

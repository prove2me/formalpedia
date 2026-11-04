-- Prove2me | solution 1 for ThreeSum.ReportingHostPrefixCatalog.rightSource_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:42:26.219204+00:00
-- url     : https://prove2.me/submissions/6a70172f-7770-441e-8c9b-51bbbe77d062

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
theorem _root_.solution {h J : ℕ} (P shift : ℤ) (C : Finset γ) (c : γ → ℤ) (q : GlobalOutput h J) :
    rightSource P shift C c q = rightSourceOf (outputOccurrences q) P shift C c := rfl
end ThreeSum.ReportingHostPrefixCatalog

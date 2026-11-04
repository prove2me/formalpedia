-- Prove2me | solution 1 for ThreeSum.ReportingHostPrefixCatalog.localLeaf_shared
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:53:43.515878+00:00
-- url     : https://prove2.me/submissions/7cf90874-2cf2-4b87-825d-0e9fff12ddfc

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixBoxes
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
import Theorems.Thm_ThreeSum_ReportingHostPrefixCatalog_localLeaf_eq_catalogLeaf

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixCatalog
open Finset LocalGraph LayerCounts BlockRows BlockIndex BlockIndexedQuery
open BlockEncoding BlockForced GlobalEncoding StoredReporting ReportingHostSuffix
set_option linter.unusedSectionVars false
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.ReportingHostPrefixCatalog
theorem _root_.solution {h J k : ℕ} (hk : k ≤ J)
    (P shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    {q q' : GlobalOutput h J} {pre pre' : List (Finset (Fin (512*h)))}
    (hp : ValidPrefix q k pre) (hp' : ValidPrefix q' k pre')
    (ho : outputOccurrences q = outputOccurrences q')
    (hkey : ofValidPrefix hk q pre hp = ofValidPrefix hk q' pre' hp') :
    LightReportingSuffixBoxes.localLeaf hk P shift B C b c q pre =
      LightReportingSuffixBoxes.localLeaf hk P shift B C b c q' pre' := by
  rw [localLeaf_eq_catalogLeaf hk P shift B C b c q pre hp,
    localLeaf_eq_catalogLeaf hk P shift B C b c q' pre' hp',ho,hkey]
end ThreeSum.ReportingHostPrefixCatalog

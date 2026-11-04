-- Prove2me | solution 1 for ThreeSum.ReportingHostLevelData.Bounds.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:57:03.208866+00:00
-- url     : https://prove2.me/submissions/b298e6b5-a213-4c51-b58b-c177a20adb08

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogQuery
import Definitions.Def_Submission_ThreeSum_LightReportingFrontierStep
import Definitions.Def_Submission_ThreeSum_ReportingHostLevelData

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostLevelData
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.ReportingHostLevelData
namespace Bounds
theorem _root_.solution {h J k baseL baseR stop stop' : ℕ} {D : Catalog}
    (H : Bounds h J k D baseL baseR stop) (hle : stop≤stop') :
    Bounds h J k D baseL baseR stop' :=
  ⟨H.left.trans hle,H.right.trans hle,H.index.trans hle,H.pointers.trans hle,H.boxes.trans hle⟩
end Bounds
end ThreeSum.ReportingHostLevelData

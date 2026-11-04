-- Prove2me | solution 1 for ThreeSum.ReportingHostLevelData.Sources.of_kept
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:57:37.364082+00:00
-- url     : https://prove2.me/submissions/61a77abe-ab72-4cd7-9e9b-20138fdf1b50

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogQuery
import Definitions.Def_Submission_ThreeSum_LightReportingFrontierStep
import Definitions.Def_Submission_ThreeSum_ReportingHostLevelData
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_storedThrough_of_on


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
namespace Sources
theorem _root_.solution {h J k baseL baseR stop : ℕ} {μ ν : ℕ→ℤ} {D : Catalog}
    {pMod shift : ℤ} {B : Finset β} {C : Finset γ} {b : β→ℤ} {c : γ→ℤ} {q : GlobalOutput h J}
    (H : Sources μ pMod shift B C b c q baseL baseR) (HB : Bounds h J k D baseL baseR stop)
    (hkeep : Kept μ ν stop) : Sources ν pMod shift B C b c q baseL baseR := by
  constructor
  · exact LightSignedLeafBatch.storedThrough_of_on H.left
      (by intro i _ hi; exact hkeep i (hi.trans_le HB.left))
  · exact LightSignedLeafBatch.storedThrough_of_on H.right
      (by intro i _ hi; exact hkeep i (hi.trans_le HB.right))
end Sources
end ThreeSum.ReportingHostLevelData

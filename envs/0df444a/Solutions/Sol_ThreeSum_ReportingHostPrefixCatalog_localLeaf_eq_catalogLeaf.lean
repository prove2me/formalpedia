-- Prove2me | solution 1 for ThreeSum.ReportingHostPrefixCatalog.localLeaf_eq_catalogLeaf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:48:26.074147+00:00
-- url     : https://prove2.me/submissions/3fdabee7-9c2c-4bd1-bea3-9d7d86e53e51

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixBoxes
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
import Theorems.Thm_ThreeSum_ReportingHostPrefixCatalog_leftSet_ofValidPrefix
import Theorems.Thm_ThreeSum_ReportingHostPrefixCatalog_rightSet_ofValidPrefix
import Theorems.Thm_ThreeSum_ReportingHostPrefixCatalog_leftSource_eq
import Theorems.Thm_ThreeSum_ReportingHostPrefixCatalog_rightSource_eq

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixCatalog
open Finset LocalGraph LayerCounts BlockRows BlockIndex BlockIndexedQuery
open BlockEncoding BlockForced GlobalEncoding StoredReporting ReportingHostSuffix
set_option linter.unusedSectionVars false
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.ReportingHostPrefixCatalog
theorem _root_.solution {h J k : ℕ} (hk : k ≤ J)
    (P shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (q : GlobalOutput h J) (pre : List (Finset (Fin (512*h)))) (hp : ValidPrefix q k pre) :
    LightReportingSuffixBoxes.localLeaf hk P shift B C b c q pre =
      leaf hk (outputOccurrences q) P shift B C b c (ofValidPrefix hk q pre hp) := by
  unfold LightReportingSuffixBoxes.localLeaf leaf
  rw [leftSet_ofValidPrefix,rightSet_ofValidPrefix,leftSource_eq,rightSource_eq]
  rfl
end ThreeSum.ReportingHostPrefixCatalog

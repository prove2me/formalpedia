-- Prove2me | solution 1 for ThreeSum.ReportingHostPositive.frontier_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:49:00.590247+00:00
-- url     : https://prove2.me/submissions/a0d401ca-f9a2-448f-b865-f11d57080e64

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogExpand
import Definitions.Def_Submission_ThreeSum_ReportingHostFrontier
import Definitions.Def_Submission_ThreeSum_ReportingHostPositive
import Theorems.Thm_ThreeSum_ReportingHostPositive_frontier_positive
import Definitions.Def_WeightedCache3SUM_Alias_fa72617747e17f03


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPositive
open Light Finset ThreeSum.SubsetAddress
open BlockForced StoredReporting GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open LightBlockChildrenIndexed ReportingHostFrontier
open scoped BigOperators
set_option linter.unusedSectionVars false
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.ReportingHostPositive
theorem _root_.solution {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (hk : k ≤ J) {pre : List (Finset (Fin (512*h)))}
    (hp : pre ∈ ReportingHostFrontier.frontier I w k) : ValidPrefix w.2.2 k pre :=
  positivePrefix_valid I w pre hk (frontier_positive _ _ hp)
end ThreeSum.ReportingHostPositive

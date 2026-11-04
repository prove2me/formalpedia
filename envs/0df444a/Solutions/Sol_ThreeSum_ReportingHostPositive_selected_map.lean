-- Prove2me | solution 1 for ThreeSum.ReportingHostPositive.selected_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:52:25.648354+00:00
-- url     : https://prove2.me/submissions/4374adff-e768-4fe0-adaf-8d4905ef99de

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogExpand
import Definitions.Def_Submission_ThreeSum_ReportingHostFrontier
import Definitions.Def_Submission_ThreeSum_ReportingHostPositive
import Theorems.Thm_ThreeSum_ReportingHostPositive_map_range_getD
import Theorems.Thm_ThreeSum_QueryCoordinates_map_range_getD


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPositive
open Light Finset ThreeSum.SubsetAddress
open BlockForced StoredReporting GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open LightBlockChildrenIndexed ReportingHostFrontier
open scoped BigOperators
set_option linter.unusedSectionVars false
namespace ThreeSum.ReportingHostPositive
theorem _root_.solution {α : Type*} (xs : List α) (fallback : α) (q : α → ℕ) :
    (LightReportingFilter.selected (fun i => q (xs[i]?.getD fallback)) xs.length).map
        (fun i => xs[i]?.getD fallback) = xs.filter (fun x => 0 < q x) := by
  change ((List.range xs.length).filter
    ((fun x : α => decide (0 < q x)) ∘ (fun i => xs[i]?.getD fallback))).map
      (fun i => xs[i]?.getD fallback) = _
  rw [← List.filter_map,map_range_getD]
end ThreeSum.ReportingHostPositive

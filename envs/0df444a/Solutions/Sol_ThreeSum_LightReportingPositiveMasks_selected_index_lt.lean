-- Prove2me | solution 1 for ThreeSum.LightReportingPositiveMasks.selected_index_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:46:54.361531+00:00
-- url     : https://prove2.me/submissions/fe65b5d1-7fad-4ee9-9b0a-b6443fa6f7b9

import Definitions.Def_Submission_ThreeSum_LightReportingGatherPair
import Definitions.Def_Submission_ThreeSum_ReportingHostPositive
import Definitions.Def_Submission_ThreeSum_LightReportingPositiveMasks
import Theorems.Thm_ThreeSum_LightReportingFilter_mem_selected
attribute [local simp] ThreeSum.LightReportingFilter.mem_selected



set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingPositiveMasks
open Light Finset ThreeSum.SubsetAddress
open BlockRows BlockIndexedQuery BlockForced StoredReporting GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open LightBlockChildrenIndexed ReportingHostPositive
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.LightReportingPositiveMasks
theorem _root_.solution {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k < J)
    {i : ℕ} (hi : i < (selectedIndices I w pre hk).length) :
    (selectedIndices I w pre hk)[i]?.getD 0 < groupSize h := by
  rw [List.getElem?_eq_getElem hi,Option.getD_some]
  exact (LightReportingFilter.mem_selected _ _ _).mp (List.getElem_mem hi) |>.1
end ThreeSum.LightReportingPositiveMasks

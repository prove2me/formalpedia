-- Prove2me | solution 1 for ThreeSum.ReportingHostFrontier.candidates_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:45:32.767142+00:00
-- url     : https://prove2.me/submissions/730c1c27-2f77-468b-8d21-215552e1da07

import Definitions.Def_Submission_ThreeSum_LightBlockChildrenIndexed
import Definitions.Def_Submission_ThreeSum_ReportingHostFrontier
import Theorems.Thm_ThreeSum_ReportingHostFrontier_children_length
import Theorems.Thm_ThreeSum_RawReporting_children_length
import Theorems.Thm_ThreeSum_Reporting_generated_candidates_length


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostFrontier
open Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostMasks BlockForced
open scoped BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
omit [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.ReportingHostFrontier
theorem _root_.solution {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (hk : k < J) :
    (candidates I w k).length = (frontier I w k).length*groupSize h := by
  rw [candidates,Reporting.generated_candidates_length,children_length _ hk]
end ThreeSum.ReportingHostFrontier

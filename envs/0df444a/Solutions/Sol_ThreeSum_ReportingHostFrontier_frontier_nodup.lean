-- Prove2me | solution 1 for ThreeSum.ReportingHostFrontier.frontier_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:59:42.973926+00:00
-- url     : https://prove2.me/submissions/14b839da-e149-435f-9c1d-4c451f186825

import Definitions.Def_Submission_ThreeSum_LightBlockChildrenIndexed
import Definitions.Def_Submission_ThreeSum_ReportingHostFrontier
import Theorems.Thm_ThreeSum_ReportingHostFrontier_children_nodup
import Theorems.Thm_ThreeSum_RawReporting_children_nodup
import Definitions.Def_WeightedCache3SUM_Alias_491c605e29e6bd9c


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostFrontier
open Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostMasks BlockForced
open scoped BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
omit [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.ReportingHostFrontier
theorem _root_.solution {h J : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (k : ℕ) : (frontier I w k).Nodup :=
  Reporting.frontier_nodup _ _ (children_nodup _) _
end ThreeSum.ReportingHostFrontier

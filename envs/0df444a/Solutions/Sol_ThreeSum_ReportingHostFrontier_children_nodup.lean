-- Prove2me | solution 1 for ThreeSum.ReportingHostFrontier.children_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:35:17.911666+00:00
-- url     : https://prove2.me/submissions/0af6184a-d22d-4a21-a542-3839c905b3e6

import Definitions.Def_Submission_ThreeSum_LightBlockChildrenIndexed
import Definitions.Def_Submission_ThreeSum_ReportingHostFrontier
import Theorems.Thm_ThreeSum_ReportingHostMasks_localChildren_nodup


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostFrontier
open Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostMasks BlockForced
open scoped BigOperators
namespace ThreeSum.ReportingHostFrontier
theorem _root_.solution {h J : ℕ} (q : GlobalOutput h J) (k : ℕ) :
    (children q k).Nodup := by
  unfold children
  split
  · exact localChildren_nodup _ _ _
  · exact List.nodup_nil
end ThreeSum.ReportingHostFrontier

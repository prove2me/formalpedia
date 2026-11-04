-- Prove2me | solution 1 for ThreeSum.ReportingHostFrontier.mem_children_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:37:41.743022+00:00
-- url     : https://prove2.me/submissions/f8fda65f-c623-4e1b-a1bb-40278513db40

import Definitions.Def_Submission_ThreeSum_LightBlockChildrenIndexed
import Definitions.Def_Submission_ThreeSum_ReportingHostFrontier
import Definitions.Def_WeightedCache3SUM_Alias_7fc1926665073fa8


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostFrontier
open Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostMasks BlockForced
open scoped BigOperators
namespace ThreeSum.ReportingHostFrontier
theorem _root_.solution {h J : ℕ} (q : GlobalOutput h J) (k : ℕ)
    (S : Finset (Fin (512*h))) : S ∈ children q k ↔ S ∈ RawReporting.children q k := by
  unfold children RawReporting.children
  split
  · exact localChildren_mem _ _ _ _
  · rfl
end ThreeSum.ReportingHostFrontier

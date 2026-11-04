-- Prove2me | solution 1 for ThreeSum.ReportingHostFrontier.total_frontier_length_le_raw_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:52:59.119731+00:00
-- url     : https://prove2.me/submissions/a684abbc-f226-422d-8a01-b829f484fce0

import Definitions.Def_Submission_ThreeSum_LightBlockChildrenIndexed
import Definitions.Def_Submission_ThreeSum_ReportingHostFrontier
import Theorems.Thm_ThreeSum_ReportingHostFrontier_frontier_length_le_domain
import Theorems.Thm_ThreeSum_RawReporting_frontier_length_le_domain


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostFrontier
open Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostMasks BlockForced
open scoped BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.ReportingHostFrontier
theorem _root_.solution {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (hk : k ≤ J) : (∑ w : Wanted h J α, (frontier I w k).length) ≤ I.card := by
  calc
    _ ≤ ∑ w : Wanted h J α, (domain I w).card := by
      exact Finset.sum_le_sum (fun w _ => frontier_length_le_domain I w hk)
    _ = _ := by
      symm
      exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
end ThreeSum.ReportingHostFrontier

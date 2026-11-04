-- Prove2me | solution 1 for ThreeSum.ReportingHostFrontier.word_children
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:42:42.523712+00:00
-- url     : https://prove2.me/submissions/9bdb877c-b8ac-4cd2-9640-4060d3370e95

import Definitions.Def_Submission_ThreeSum_LightBlockChildrenIndexed
import Definitions.Def_Submission_ThreeSum_ReportingHostFrontier
import Theorems.Thm_ThreeSum_ReportingHostFrontier_mem_children_iff
import Definitions.Def_WeightedCache3SUM_Alias_658daccd3d316101


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostFrontier
open Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostMasks BlockForced
open scoped BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.ReportingHostFrontier
theorem _root_.solution {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (r : RawItem h J α β γ) (hr : r ∈ domain I w) (j : ℕ) (hj : j < J) :
    (word r)[j]'(by rw [word,partitionWord_length]; exact hj) ∈ children w.2.2 j :=
  (mem_children_iff _ _ _).mpr (RawReporting.word_children I w r hr j hj)
end ThreeSum.ReportingHostFrontier

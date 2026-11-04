-- Prove2me | solution 1 for ThreeSum.ReportingHostPositive.positiveChildren_eq_filter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:57:48.865018+00:00
-- url     : https://prove2.me/submissions/e7201221-c49d-48a1-b47c-c2235a725539

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogExpand
import Definitions.Def_Submission_ThreeSum_ReportingHostFrontier
import Definitions.Def_Submission_ThreeSum_ReportingHostPositive
import Theorems.Thm_ThreeSum_ReportingHostPositive_selected_map
import Theorems.Thm_Light_Ends_next


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
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k < J) :
    positiveChildren I w pre hk =
      (childPrefixes w.2.2 pre hk).filter (fun next => 0 < prefixQuery I w (k+1) next) := by
  unfold positiveChildren
  change (LightReportingFilter.selected
    (fun i => prefixQuery I w (k+1) ((childPrefixes w.2.2 pre hk)[i]?.getD [])) (groupSize h)).map
      (fun i => (childPrefixes w.2.2 pre hk)[i]?.getD []) = _
  rw [← childPrefixes_length w.2.2 pre hk]
  exact selected_map (childPrefixes w.2.2 pre hk) [] (prefixQuery I w (k+1))
end ThreeSum.ReportingHostPositive

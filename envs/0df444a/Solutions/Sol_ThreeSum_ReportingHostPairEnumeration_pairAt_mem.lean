-- Prove2me | solution 1 for ThreeSum.ReportingHostPairEnumeration.pairAt_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:50:28.766132+00:00
-- url     : https://prove2.me/submissions/02077830-af4f-4b76-abea-df16c91bed70

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_ReportingHostPairEnumeration
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_rightAt_eq_get
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet



set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPairEnumeration
open Finset ThreeSum.SubsetAddress LayerCounts LocalGraph
set_option linter.unusedSimpArgs false
namespace ThreeSum.ReportingHostPairEnumeration
theorem _root_.solution {L h i j : ℕ} (hi : i < L.choose h) (hj : j < (L-h).choose h) :
    (leftAt L h i,rightAt L h i j) ∈ edgeSet L h := by
  rw [LayerCounts.mem_edgeSet]
  refine ⟨leftAt_card hi,?_⟩
  rw [rightAt_eq_get hi hj]
  exact (rights_mem _ _).mp (List.getElem_mem _)
end ThreeSum.ReportingHostPairEnumeration

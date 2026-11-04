-- Prove2me | solution 1 for ThreeSum.ReportingHostFrontier.children_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:36:09.974633+00:00
-- url     : https://prove2.me/submissions/3594e930-d954-4cf1-8f7e-80486c07dd18

import Definitions.Def_Submission_ThreeSum_LightBlockChildrenIndexed
import Definitions.Def_Submission_ThreeSum_ReportingHostFrontier
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_ReportingHostMasks_localChildren_length
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.ReportingHostMasks.localChildren_length



set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostFrontier
open Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostMasks BlockForced
open scoped BigOperators
namespace ThreeSum.ReportingHostFrontier
theorem _root_.solution {h J k : ℕ} (q : GlobalOutput h J) (hk : k < J) :
    (children q k).length = groupSize h := by
  rw [children,dif_pos hk,localChildren_length]
  have hc : (outputRows q ⟨k,hk⟩).card = 2*h :=
    LayerCounts.mem_vertices.mp (q ⟨k,hk⟩).2.property
  rw [hc]
  rfl
end ThreeSum.ReportingHostFrontier

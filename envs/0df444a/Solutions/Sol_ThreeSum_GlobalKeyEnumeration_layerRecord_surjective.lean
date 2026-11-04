-- Prove2me | solution 1 for ThreeSum.GlobalKeyEnumeration.layerRecord_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:14:48.791048+00:00
-- url     : https://prove2.me/submissions/21d654d1-02b0-4559-9efa-4ac406a0e2f0

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LocalMaskGraph_setAt_complete
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.GlobalKeyEnumeration
open GlobalEncoding LocalGraph LocalCoverBounds LocalHashMoments
open RadixKeyLists
open scoped BigOperators
set_option maxHeartbeats 1800000
namespace ThreeSum.GlobalKeyEnumeration
theorem _root_.solution (h : ℕ) : Function.Surjective (layerRecord h) := by
  intro Q
  obtain ⟨i,hi,he⟩ := LocalMaskGraph.setAt_complete Q.val
    (LayerCounts.mem_vertices.mp Q.property)
  exact ⟨⟨i,hi⟩,Subtype.ext he⟩
end ThreeSum.GlobalKeyEnumeration

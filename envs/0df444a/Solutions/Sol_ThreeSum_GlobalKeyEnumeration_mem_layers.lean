-- Prove2me | solution 1 for ThreeSum.GlobalKeyEnumeration.mem_layers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:18:57.107787+00:00
-- url     : https://prove2.me/submissions/ee40b2d6-db70-43fb-89e3-b21cb434bdca

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Theorems.Thm_ThreeSum_GlobalKeyEnumeration_layerRecord_surjective

set_option autoImplicit false
open ThreeSum ThreeSum.GlobalKeyEnumeration
open GlobalEncoding LocalGraph LocalCoverBounds LocalHashMoments
open RadixKeyLists
open scoped BigOperators
set_option maxHeartbeats 1800000
namespace ThreeSum.GlobalKeyEnumeration
theorem _root_.solution (h : ℕ) (Q : {Q // Q ∈ LayerCounts.vertices (512*h) (2*h)}) :
    Q ∈ layers h := by
  obtain ⟨i,rfl⟩ := layerRecord_surjective h Q
  exact List.mem_ofFn.mpr ⟨i,rfl⟩
end ThreeSum.GlobalKeyEnumeration

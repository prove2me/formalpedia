-- Prove2me | solution 1 for QEC.Locality.canonicalEdgeRegions_isEdgeDivision
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:25:57.896745+00:00
-- url     : https://prove2.me/submissions/3e6d6ace-116a-4d8c-ae39-22fd93fb13f7

import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Theorems.Thm_QEC_Locality_canonicalEdgeOwner_reverse
import Theorems.Thm_QEC_Locality_mem_canonicalEdgeRegion_iff
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_mem_directedEdgeFinset_iff


set_option autoImplicit false
open QEC QEC.Locality
universe u w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution (G : ConnectivityGraph ι) :
    IsEdgeDivision G (canonicalEdgeRegion G) (canonicalEdgeRepresentatives G) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro owner _ edge hedge
    exact (mem_canonicalEdgeRegion_iff G owner edge).1 hedge |>.1
  · intro owner _ x y
    rw [mem_canonicalEdgeRegion_iff, mem_canonicalEdgeRegion_iff]
    constructor
    · rintro ⟨hxy, howner⟩
      exact ⟨(mem_directedEdgeFinset_iff G y x).2
        (G.symmetric ((mem_directedEdgeFinset_iff G x y).1 hxy)),
        (canonicalEdgeOwner_reverse (x, y)).trans howner⟩
    · rintro ⟨hyx, howner⟩
      exact ⟨(mem_directedEdgeFinset_iff G x y).2
        (G.symmetric ((mem_directedEdgeFinset_iff G y x).1 hyx)),
        (canonicalEdgeOwner_reverse (y, x)).trans howner⟩
  · intro edge hedge
    refine ⟨canonicalEdgeOwner edge, ?_, ?_⟩
    · constructor
      · exact Finset.mem_image.2 ⟨edge, hedge, rfl⟩
      · exact (mem_canonicalEdgeRegion_iff G (canonicalEdgeOwner edge) edge).2
          ⟨hedge, rfl⟩
    · intro owner howner
      exact (mem_canonicalEdgeRegion_iff G owner edge).1 howner.2 |>.2.symm
end QEC.Locality

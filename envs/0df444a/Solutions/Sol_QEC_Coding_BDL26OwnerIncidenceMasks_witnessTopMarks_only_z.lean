-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerIncidenceMasks.witnessTopMarks_only_z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:38:39.630836+00:00
-- url     : https://prove2.me/submissions/07f19722-f400-4942-97f3-2f442ccf1597

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_witnessTopOwner_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerParentObstruction BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26OwnerIncidenceMasks
theorem _root_.solution (v : Vertex (state scaleFive 3).presentation)
    (hv : v ∈ witnessTopMarks) : ∃ z, v = Vertex.z z := by
  have hm := (Finset.mem_filter.mp hv).2
  rcases hm with ⟨p, rfl, _⟩ | ⟨j, rfl, _⟩ | ⟨j, p, rfl, _⟩
  · exact ⟨p.1, witnessTopOwner_eq p⟩
  · exact ⟨_, rfl⟩
  · exact ⟨p.1, witnessTopOwner_eq p⟩
end QEC.Coding.BDL26OwnerIncidenceMasks

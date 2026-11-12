-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.base_parent_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:11:38.939537+00:00
-- url     : https://prove2.me/submissions/f78ab3f0-e878-4cc5-a89f-8004cd95526c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution (v : GraphVertex S 2) (u : GraphVertex S 1)
    (hp : parent S 1 v = some u) :
    (decodingGraph S (n + 2)).adjacent (physicalNode S n 0 v) (oneNode S n u) := by
  apply Or.inr
  apply Or.inr
  refine ⟨⟨1, by omega⟩, ?_⟩
  exact (parent_interLevel_iff S (n + 2) ⟨1, by omega⟩ u v).mp hp
end QEC.Coding.BDL26CanonicalHistoryMarks

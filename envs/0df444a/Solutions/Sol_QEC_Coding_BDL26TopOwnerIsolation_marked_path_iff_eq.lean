-- Prove2me | solution 1 for QEC.Coding.BDL26TopOwnerIsolation.marked_path_iff_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:39:44.740204+00:00
-- url     : https://prove2.me/submissions/5e86816c-535f-4cb5-87c1-39143c11a2d0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
import Theorems.Thm_QEC_Coding_BDL26TopOwnerIsolation_no_marked_neighbor
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26TopOwnerIsolation
open BDL26FiniteTannerSquare BDL26DecodingGraph MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26TopOwnerIsolation
theorem _root_.solution (M : Finset Node) (hM : TopMarksAreZ M)
    (z : (state scaleFive 3).presentation.Z)
    (hparent : parent scaleFive 3 (Vertex.z z) = none)
    (ha : topNode (.z z) ∈ M) (w : {w : Node // w ∈ M}) :
    Relation.ReflTransGen (markedAdjacent M) ⟨topNode (.z z),ha⟩ w ↔
      w = ⟨topNode (.z z),ha⟩ := by
  constructor
  · intro hpath
    rcases hpath.cases_head with heq | ⟨next,hedge,_⟩
    · exact heq.symm
    · exact (no_marked_neighbor M hM z hparent next.val next.property hedge).elim
  · rintro rfl
    exact Relation.ReflTransGen.refl
end QEC.Coding.BDL26TopOwnerIsolation

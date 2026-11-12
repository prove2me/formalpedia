-- Prove2me | solution 1 for QEC.Coding.BDL26UniformTopOwnerIsolation.marked_path_iff_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:01:27.850772+00:00
-- url     : https://prove2.me/submissions/f181d7de-cf04-4254-a6dd-88ec43ae06da

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Theorems.Thm_QEC_Coding_BDL26UniformTopOwnerIsolation_no_marked_neighbor
import Theorems.Thm_QEC_Coding_BDL26TopOwnerIsolation_no_marked_neighbor
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformTopOwnerIsolation
open BDL26FiniteTannerSquare BDL26DecodingGraph MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26UniformTopOwnerIsolation
theorem _root_.solution (S : OddScale) (n : Nat) (M : Finset (Node S n)) (hM : TopMarksAreZ S n M)
    (z : (state S n).presentation.Z)
    (hparent : parent S n (Vertex.z z) = none)
    (ha : topNode S n (.z z) ∈ M) (w : {w : Node S n // w ∈ M}) :
    Relation.ReflTransGen (markedAdjacent S n M) ⟨topNode S n (.z z),ha⟩ w ↔
      w = ⟨topNode S n (.z z),ha⟩ := by
  constructor
  · intro hpath
    rcases hpath.cases_head with heq | ⟨next,hedge,_⟩
    · exact heq.symm
    · exact (no_marked_neighbor S n M hM z hparent next.val next.property hedge).elim
  · rintro rfl
    exact Relation.ReflTransGen.refl
end QEC.Coding.BDL26UniformTopOwnerIsolation

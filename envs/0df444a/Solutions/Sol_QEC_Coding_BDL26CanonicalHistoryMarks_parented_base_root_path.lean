-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.parented_base_root_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:25:19.735042+00:00
-- url     : https://prove2.me/submissions/2c86ee44-d5a1-4b67-b156-7e7427fa04db

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_parented_base_two_edges
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution (v : GraphVertex S 2) (hv : v ∈ baseMarks S n sigma)
    (u : GraphVertex S 1) (hp : parent S 1 v = some u) :
    Relation.ReflTransGen (markedAdjacent S n sigma) (physicalNode S n 0 v) (root S n) := by
  have he := parented_base_two_edges S n sigma v hv u hp
  exact (Relation.ReflTransGen.single he.1).trans (Relation.ReflTransGen.single he.2)
end QEC.Coding.BDL26CanonicalHistoryMarks

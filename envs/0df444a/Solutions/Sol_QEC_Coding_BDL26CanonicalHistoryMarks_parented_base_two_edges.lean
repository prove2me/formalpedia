-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.parented_base_two_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:19:47.332831+00:00
-- url     : https://prove2.me/submissions/ff90c96a-c78e-4913-b299-a6a2405d7d1c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_oneMarks
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_marks_physical
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_marks_one
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_root_marked_iff
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_base_parent_edge
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_one_root_edge

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution (v : GraphVertex S 2) (hv : v ∈ baseMarks S n sigma)
    (u : GraphVertex S 1) (hp : parent S 1 v = some u) :
    markedAdjacent S n sigma (physicalNode S n 0 v) (oneNode S n u) ∧
    markedAdjacent S n sigma (oneNode S n u) (root S n) := by
  have hu := (mem_oneMarks S n sigma u).mpr ⟨v, hv, hp⟩
  have hroot := (root_marked_iff S n sigma).mpr ⟨u, hu⟩
  have hv' := (mem_marks_physical S n sigma 0 v).mpr hv
  have hu' := (mem_marks_one S n sigma u).mpr hu
  exact ⟨⟨base_parent_edge S n v u hp, hv', hu'⟩,
    ⟨one_root_edge S n u, hu', hroot⟩⟩
end QEC.Coding.BDL26CanonicalHistoryMarks

-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.oneMarks_in_rootComponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:11:52.556146+00:00
-- url     : https://prove2.me/submissions/e8c870d4-4d98-48e8-a292-7e909b69ed56

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_marks_one
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_root_marked_iff
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_one_root_edge
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_rootComponent

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution (u : GraphVertex S 1) (hu : u ∈ oneMarks S n sigma) :
    oneNode S n u ∈ rootComponent S n sigma := by
  have hr := (root_marked_iff S n sigma).mpr ⟨u, hu⟩
  have hm := (mem_marks_one S n sigma u).mpr hu
  exact (mem_rootComponent S n sigma _).mpr ⟨hr, hm,
    Relation.ReflTransGen.single ⟨one_root_edge S n u, hm, hr⟩⟩
end QEC.Coding.BDL26CanonicalHistoryMarks

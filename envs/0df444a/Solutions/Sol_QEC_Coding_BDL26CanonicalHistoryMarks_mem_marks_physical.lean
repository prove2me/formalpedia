-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.mem_marks_physical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:14:29.812514+00:00
-- url     : https://prove2.me/submissions/bbc8aa15-bfe8-48af-ae87-2484838041f0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_rootImage_level
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_physicalNodes

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution (i : LevelIndex n) (v : GraphVertex S (i.val + 2)) :
    physicalNode S n i v ∈ marks S n sigma ↔ v ∈ physicalMarks S n sigma i := by
  constructor
  · intro hm
    rcases Finset.mem_union.mp hm with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact (mem_physicalNodes S n sigma i v).mp h
      · obtain ⟨u, _, he⟩ := Finset.mem_image.mp h
        have hl := congrArg (fun w : Node S n => w.1.val) he
        change 1 = i.val + 2 at hl
        omega
    · have hl : i.val + 2 = 0 := rootImage_level S n sigma _ h
      omega
  · intro hv
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
      (Or.inl ((mem_physicalNodes S n sigma i v).mpr hv))))
end QEC.Coding.BDL26CanonicalHistoryMarks

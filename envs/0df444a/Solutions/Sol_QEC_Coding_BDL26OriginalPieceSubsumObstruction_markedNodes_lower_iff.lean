-- Prove2me | solution 1 for QEC.Coding.BDL26OriginalPieceSubsumObstruction.markedNodes_lower_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:07:51.023713+00:00
-- url     : https://prove2.me/submissions/b21a5bd7-af3f-433c-9d85-4e6c2f4fd537

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_OriginalPieceSubsumObstruction
section
namespace QEC.Coding.BDL26OriginalPieceSubsumObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators
private theorem includeLowerNode_injective (S : OddScale) (j : Nat) :
    Function.Injective (includeLowerNode S j) := by
  rintro ⟨i,v⟩ ⟨k,w⟩ he
  have hi : i = k := Fin.ext (congrArg (fun u : UniformNode S j => u.1.val) he)
  subst k
  have hv : v = w := by cases he; rfl
  subst w
  rfl
end QEC.Coding.BDL26OriginalPieceSubsumObstruction
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OriginalPieceSubsumObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26OriginalPieceSubsumObstruction
theorem _root_.solution (S : OddScale) (j : Nat)
    (lower : Finset (StrictLowerNode S j)) (v : StrictLowerNode S j) :
    includeLowerNode S j v ∈ markedNodes S j lower ↔ v ∈ lower := by
  constructor
  · intro hm
    rcases Finset.mem_union.mp hm with ht | hl
    · obtain ⟨w,_,he⟩ := Finset.mem_image.mp ht
      have hv := congrArg (fun u : UniformNode S j => u.1.val) he
      change 2*j+4 = v.1.val at hv
      have hlt := v.1.isLt
      omega
    · obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hl
      exact (includeLowerNode_injective S j he) ▸ hw
  · intro hv
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩)
end QEC.Coding.BDL26OriginalPieceSubsumObstruction

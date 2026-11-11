-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.unparented_base_syndrome_guard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:41:02.8035+00:00
-- url     : https://prove2.me/submissions/15097c8c-40e0-47c7-8055-745f3be7bce8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_baseMarks

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution
    (v : GraphVertex S 2) (hv : parent S 1 v = none)
    (p : FamilyZ S (n + 2) (LevelTwoHistory.physicalLevel (0 : LevelIndex n)))
    (ho : baseSyndromeOwner S n p = v) (hp : (baseInput S n sigma).val p ≠ 0) :
    v ∈ baseMarks S n sigma ∧ parent S 1 v = none :=
  ⟨(mem_baseMarks S n sigma v).mpr (Or.inl ⟨p, ho, hp⟩), hv⟩
end QEC.Coding.BDL26CanonicalHistoryMarks

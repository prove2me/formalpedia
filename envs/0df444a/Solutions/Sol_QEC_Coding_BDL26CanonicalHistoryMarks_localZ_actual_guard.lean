-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.localZ_actual_guard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:31:30.577479+00:00
-- url     : https://prove2.me/submissions/b66784d6-8020-43bd-8c24-372ed4cc2a09

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_localZ_unparented
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_localZCoordinate_owner
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_marks_physical
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_unparented_base_syndrome_guard


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution (S : OddScale) (n : Nat) (sigma : Input S n) (x : BaseX)
    (f : DoubleCylinderFace baseTannerSquarePresentation x S)
    (h : (baseInput S n sigma).val (localZCoordinate S n x f) ≠ 0) :
    physicalNode S n 0 (localZ S x f) ∈ marks S n sigma ∧
      parent S 1 (localZ S x f) = none := by
  have hm := unparented_base_syndrome_guard S n sigma (localZ S x f)
    (localZ_unparented S x f) (localZCoordinate S n x f)
    (localZCoordinate_owner S n x f) h
  exact ⟨(mem_marks_physical S n sigma 0 _).mpr hm.1, hm.2⟩
end QEC.Coding.BDL26CanonicalHistoryMarks

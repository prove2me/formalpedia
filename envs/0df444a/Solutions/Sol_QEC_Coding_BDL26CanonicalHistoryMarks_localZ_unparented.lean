-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.localZ_unparented
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:25:44.148832+00:00
-- url     : https://prove2.me/submissions/fddd05f3-66ae-43e3-8285-c58c491efecc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution (S : OddScale) (x : BaseX)
    (f : DoubleCylinderFace baseTannerSquarePresentation x S) :
    parent S 1 (localZ S x f) = none := rfl
end QEC.Coding.BDL26CanonicalHistoryMarks

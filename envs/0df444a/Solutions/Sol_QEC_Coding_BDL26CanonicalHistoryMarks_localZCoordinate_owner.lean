-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.localZCoordinate_owner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:25:52.440207+00:00
-- url     : https://prove2.me/submissions/1c422de9-6490-4c98-8c64-2b8d3806a61a

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
theorem _root_.solution (S : OddScale) (n : Nat) (x : BaseX)
    (f : DoubleCylinderFace baseTannerSquarePresentation x S) :
    baseSyndromeOwner S n (localZCoordinate S n x f) = localZ S x f := rfl
end QEC.Coding.BDL26CanonicalHistoryMarks

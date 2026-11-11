-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.markedAdjacent_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T04:56:45.506196+00:00
-- url     : https://prove2.me/submissions/d4a4b8f6-0daf-4c6b-9bbb-b970abc3eb72

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution (u v : Node S n) : markedAdjacent S n sigma u v ↔
    (decodingGraph S (n + 2)).adjacent u v ∧ u ∈ marks S n sigma ∧ v ∈ marks S n sigma := Iff.rfl
end QEC.Coding.BDL26CanonicalHistoryMarks

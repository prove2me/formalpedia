-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.rzPropagation_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:46:31.542407+00:00
-- url     : https://prove2.me/submissions/5f67943a-4d60-451c-becb-46df170b4b7c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Steps

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26RXDecoderAdapter BDL26RZDecoderAdapter
open BDL26RXCoarseInfluence BDL26RXInfluenceBounds MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
theorem _root_.solution (h : ¬ i.val % 2 = 0)
    (A : Finset (FamilyZ S depth i.succ)) :
    (rzPropagation S depth i h A).card ≤ A.card := Finset.card_image_le
end QEC.Coding.BDL26HistorySyndromeSensitivity

-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.rxPropagation_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:59:19.695437+00:00
-- url     : https://prove2.me/submissions/77d8e7ba-d3c8-4ef7-b567-093919f3a456

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Steps
import Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_readers_card_le


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
theorem _root_.solution (h : i.val % 2 = 0)
    (A : Finset (FamilyZ S depth i.succ)) :
    (rxPropagation S depth i h A).card ≤ 57 * A.card := by
  exact (Finset.card_biUnion_le_card_mul A (readers S depth i h) 57
    (fun p _ => readers_card_le S depth i h p)).trans_eq (Nat.mul_comm _ _)
end QEC.Coding.BDL26HistorySyndromeSensitivity

-- Prove2me | solution 1 for QEC.Coding.BDL26PairedHistoryQueryCone.liftQueries_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:43:52.011428+00:00
-- url     : https://prove2.me/submissions/d3b60504-258f-4b16-ac82-2edb1c482d72

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_LocalReads
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_coarseRead_card

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26RXCoarseInfluence
open BDL26RXInfluenceBounds BDL26GraphQuantitativeBounds
open MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26PairedHistoryQueryCone
theorem _root_.solution (A : Finset (FamilyZ S depth i.castSucc)) :
    (liftQueries S depth i A).card ≤ queryBlockBound S * A.card := by
  exact (Finset.card_biUnion_le_card_mul A _ (queryBlockBound S)
    (fun z _ => coarseRead_card S depth i z)).trans_eq (Nat.mul_comm _ _)
end QEC.Coding.BDL26PairedHistoryQueryCone

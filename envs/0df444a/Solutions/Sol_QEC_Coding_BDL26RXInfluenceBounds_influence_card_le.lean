-- Prove2me | solution 1 for QEC.Coding.BDL26RXInfluenceBounds.influence_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:59:13.981262+00:00
-- url     : https://prove2.me/submissions/e61e1fbc-c9d4-4efe-a228-284219ee5653

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
import Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_readers_card_le
import Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_basisSyndrome_weight_le_four
import Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_influence_eq_readers

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXInfluenceBounds
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter BDL26RXCoarseInfluence BDL26BoundedValence
open BDL26GraphQuantitativeBounds BDL26RZMap1CoordinateBridge
open MultiscaleDecoder RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)
namespace QEC.Coding.BDL26RXInfluenceBounds
theorem _root_.solution (q : FamilyQ S depth i.succ) : (influence S depth i h q).card ≤ 228 := by
  rw [influence_eq_readers]
  have hc := Finset.card_biUnion_le_card_mul (hammingSupport (basisSyndrome S depth i q))
    (readers S depth i h) 57 (fun p _ => readers_card_le S depth i h p)
  have hb := basisSyndrome_weight_le_four S depth i q
  change (hammingSupport (basisSyndrome S depth i q)).card ≤ 4 at hb
  omega
end QEC.Coding.BDL26RXInfluenceBounds

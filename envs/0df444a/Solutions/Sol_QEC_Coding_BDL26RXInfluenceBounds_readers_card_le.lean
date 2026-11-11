-- Prove2me | solution 1 for QEC.Coding.BDL26RXInfluenceBounds.readers_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:53:31.483546+00:00
-- url     : https://prove2.me/submissions/c20b37c7-8d8f-4657-83fa-cda9e4c7c91e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
import Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_distance_le_two_mem_forwardTwo
import Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_forwardTwo_card_le
import Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_actual_outNeighbors_card_le
import Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_readRegion_iff_distance
import Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_coarseCenter_injective
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
theorem _root_.solution (p : FamilyZ S depth i.succ) : (readers S depth i h p).card ≤ 57 := by
  have hc : (readers S depth i h p).card ≤
      (forwardTwo (rxData S depth i h).levelGraph.graph ((rxData S depth i h).topCenter p)).card := by
    apply Finset.card_le_card_of_injOn (rxData S depth i h).coarseCenter
    · intro z hz
      exact distance_le_two_mem_forwardTwo _ _ _
        ((readRegion_iff_distance S depth i h p z).mp (Finset.mem_filter.mp hz).2)
    · exact (coarseCenter_injective S depth i h).injOn
  exact hc.trans (forwardTwo_card_le _ (actual_outNeighbors_card_le S depth i h) _)
end QEC.Coding.BDL26RXInfluenceBounds

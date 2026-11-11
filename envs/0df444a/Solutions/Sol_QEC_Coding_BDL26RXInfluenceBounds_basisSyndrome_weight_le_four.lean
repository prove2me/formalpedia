-- Prove2me | solution 1 for QEC.Coding.BDL26RXInfluenceBounds.basisSyndrome_weight_le_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:49:36.077215+00:00
-- url     : https://prove2.me/submissions/8346188f-97f1-47d6-ba7d-30ccc7fe1a71

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_state_boundedValence
import Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_basis_coboundary_weight


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
theorem _root_.solution (q : FamilyQ S depth i.succ) :
    HammingWeight (basisSyndrome S depth i q) ≤ 4 := by
  unfold basisSyndrome
  rw [indexedFamily_coboundary1, BDL26UniformHistoryObstruction.basis_coboundary_weight]
  exact ((state_boundedValence S i.succ.val).2.2 q).2.1
end QEC.Coding.BDL26RXInfluenceBounds

-- Prove2me | solution 1 for QEC.Coding.BDL26UniformHistoryObstruction.lowerSyndrome_weight_le_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:54:34.814094+00:00
-- url     : https://prove2.me/submissions/2abfae9f-06fd-4b11-8869-a063d8e178fd

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_lowerSyndrome_weight_eq
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_state_boundedValence


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26UniformHistoryObstruction
theorem _root_.solution (S : OddScale) (j : Nat) :
    HammingWeight (lowerSyndrome S j).val ≤ 4 := by
  rw [lowerSyndrome_weight_eq]
  exact ((state_boundedValence S (2 * j + 3)).2.2 (lowerBasis S j)).2.1
end QEC.Coding.BDL26UniformHistoryObstruction

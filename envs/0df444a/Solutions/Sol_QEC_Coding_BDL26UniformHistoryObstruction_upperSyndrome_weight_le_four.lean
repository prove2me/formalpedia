-- Prove2me | solution 1 for QEC.Coding.BDL26UniformHistoryObstruction.upperSyndrome_weight_le_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:00:12.516199+00:00
-- url     : https://prove2.me/submissions/a8cec844-2543-4c2e-a404-916d49feb41d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_lowerSyndrome_weight_le_four
import Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_upperSyndrome_weight_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26UniformHistoryObstruction
theorem _root_.solution (S : OddScale) (j : Nat) :
    HammingWeight (upperSyndrome S j).val ≤ 4 := by
  rw [upperSyndrome_weight_eq]
  exact lowerSyndrome_weight_le_four S j
end QEC.Coding.BDL26UniformHistoryObstruction

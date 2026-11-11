-- Prove2me | solution 1 for QEC.Coding.BDL26UniformHistoryObstruction.topMarks_active
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:58:33.813193+00:00
-- url     : https://prove2.me/submissions/684c951f-cf22-4115-a3b0-4ce2f860f438

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_outputMarks_contains_syndrome


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks
open BDL26OwnerParentObstruction BDL26ReplacementSupport BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open BDL26XLocalRadialParity BDL26XLocalConnectingWeight
open MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26UniformHistoryObstruction
theorem _root_.solution (S : OddScale) (j : Nat)
    (p : FamilyZ S (2 * j + 4) (TopIndex (2 * j + 4)))
    (hp : (upperSyndrome S j).val p ≠ 0) : topOwner S j p ∈ topMarks S j := by
  apply outputMarks_contains_syndrome
  have hi := (actualStep_relation S (2 * j + 4) ⟨2 * j + 3, by omega⟩).input_eq
    (upperSyndrome S j)
  change (topOutput S j).input = upperSyndrome S j at hi
  rw [hi]
  exact hp
end QEC.Coding.BDL26UniformHistoryObstruction

-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonDepth.zero_seed_c2_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:28:51.523924+00:00
-- url     : https://prove2.me/submissions/7c3549cd-2a7d-4aa4-b1c9-d0180b8fd572

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonResponse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualInputs_readout
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_differential_weight
import Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_actualHistory_c2_weight
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonDepth
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open BDL26LocalBackgroundComparisonResponse
open scoped Classical BigOperators
namespace QEC.Coding.BDL26LocalBackgroundComparisonDepth
theorem _root_.solution (S : OddScale) (n : Nat) (g : W S n) :
    2 ^ ((n+1)/2) * HammingWeight
      (BDL26AllDepthBottomComparisonStability.baseReadout S n
        (perturbTop S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) g)) ≤
      4 * HammingWeight g := by
  let tau : TopInput S n :=
    perturbTop S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) g
  have history := BDL26UniformHistoryObstruction.actualHistory_c2_weight S n tau
  change 2 ^ ((n+1)/2) * HammingWeight (actualReadout S n tau 0) ≤ HammingWeight tau.val at history
  rw [actualInputs_readout] at history
  have top : tau.val = (indexedFamily S (n+2)).coboundary1 (TopIndex (n+2)) g := by
    change (0 : (indexedFamily S (n+2)).Cochain2 (TopIndex (n+2)))+_=_
    exact zero_add _
  rw [top] at history
  have degree := differential_weight S (n+2) (Fin.last (n+1)) g
  exact history.trans degree
end QEC.Coding.BDL26LocalBackgroundComparisonDepth

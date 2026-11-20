-- Prove2me | solution 1 for QEC.Coding.BDL26AllDepthBottomComparisonStability.original_input_single_flip_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T15:00:39.880795+00:00
-- url     : https://prove2.me/submissions/0711070b-04a1-4354-912b-f7cdebe42fbe

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_EvenC4OldXEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AllDepthBottomComparisonStability
import Theorems.Thm_QEC_Coding_BDL26AllDepthBottomComparisonStability_zero_base_single_flip_stable
import Theorems.Thm_QEC_Coding_BDL26AllDepthBottomComparisonStability_baseReadout_original_FIRST
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26AllDepthBottomComparisonStability
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
namespace QEC.Coding.BDL26AllDepthBottomComparisonStability
theorem _root_.solution (S : OddScale) (n : Nat) (large : 16≤S.half)
    (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (zero : BDL26ActualFailureReadout.firstReadout S n u=0) :
    SingleFlipStable S n (BDL26ActualFailureReadout.input S n u) :=
  zero_base_single_flip_stable S n large _
    ((baseReadout_original_FIRST S n u).trans zero)
end QEC.Coding.BDL26AllDepthBottomComparisonStability

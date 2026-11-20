-- Prove2me | solution 1 for QEC.Coding.BDL26AllDepthBottomComparisonStability.baseReadout_original_FIRST
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:09:27.945757+00:00
-- url     : https://prove2.me/submissions/ebf1acdb-0247-4402-87d5-a5b46b90259c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_EvenC4OldXEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AllDepthBottomComparisonStability

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26AllDepthBottomComparisonStability
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
namespace QEC.Coding.BDL26AllDepthBottomComparisonStability
theorem _root_.solution (S : OddScale) (n : Nat)
    (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n) :
    baseReadout S n (BDL26ActualFailureReadout.input S n u)=
      BDL26ActualFailureReadout.firstReadout S n u := rfl
end QEC.Coding.BDL26AllDepthBottomComparisonStability

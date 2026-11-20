-- Prove2me | solution 1 for QEC.Coding.BDL26ActualFailureReadout.physical_Y_iXZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:33:18.48173+00:00
-- url     : https://prove2.me/submissions/1fc9042c-1152-47e2-b33c-198b93717dbe

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoLocalBranchEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoOldXStarEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_actual_Y_operator


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ActualFailureReadout
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian
open scoped Classical BigOperators
open QEC.Semantics BDL26PairedDecoderPhase
namespace QEC.Coding.BDL26ActualFailureReadout
theorem _root_.solution (S : OddScale) (n : Nat) (q : Physical S (n+2)) :
    CSSDaviesLocality.coupling q .y=Complex.I •
      (Qubit.localX q*Qubit.localZ q) := actual_Y_operator S n q
end QEC.Coding.BDL26ActualFailureReadout

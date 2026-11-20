-- Prove2me | solution 1 for QEC.Coding.BDL26RXQEdgePairTransport.path_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:31:57.308176+00:00
-- url     : https://prove2.me/submissions/8b876e17-b5bc-4043-b741-d77886bac1d9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_HigherRXFaceTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RZLocalEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXQEdgePairTransport

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXQEdgePairTransport
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26LocalizedHistoryErrorDescent BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26OwnerIncidenceMasks BDL26HistoryLogicalResidual BDL26TannerLocalRegularity
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXQEdgePairTransport
theorem _root_.solution (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (top : LocalizedWord S N sigma tau (TopIndex N)) {a b : LevelIndex N} (hab : a=b) :
    cast (congrArg (LocalizedWord S N sigma tau) hab) (path S N sigma tau top a)=
      path S N sigma tau top b := by
  cases hab
  rfl
end QEC.Coding.BDL26RXQEdgePairTransport

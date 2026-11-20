-- Prove2me | solution 1 for QEC.Coding.BDL26RXQEdgePairTransport.localized_cast_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:41:43.546999+00:00
-- url     : https://prove2.me/submissions/ff8b33f2-c2dd-4e4d-881a-250f3a4726b2

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
theorem _root_.solution {S : OddScale} {N : Nat} {sigma tau : TopInput S N}
    {a b : LevelIndex N} (hab : a=b) (w : LocalizedWord S N sigma tau a)
    (hw : w.word=0) : (cast (congrArg (LocalizedWord S N sigma tau) hab) w).word=0 := by
  cases hab
  exact hw
end QEC.Coding.BDL26RXQEdgePairTransport

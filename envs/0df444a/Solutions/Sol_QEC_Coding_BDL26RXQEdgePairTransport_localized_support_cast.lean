-- Prove2me | solution 1 for QEC.Coding.BDL26RXQEdgePairTransport.localized_support_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:29:42.203727+00:00
-- url     : https://prove2.me/submissions/942027c4-cc5e-42ad-8a95-3ea62d5fad91

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
    {a b : LevelIndex N} (hab : a=b) (w : LocalizedWord S N sigma tau a) :
    HEq (hammingSupport (cast (congrArg (LocalizedWord S N sigma tau) hab) w).word)
      (hammingSupport w.word) := by
  cases hab
  rfl
end QEC.Coding.BDL26RXQEdgePairTransport

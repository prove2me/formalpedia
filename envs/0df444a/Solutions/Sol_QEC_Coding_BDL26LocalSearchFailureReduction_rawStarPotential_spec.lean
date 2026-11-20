-- Prove2me | solution 1 for QEC.Coding.BDL26LocalSearchFailureReduction.rawStarPotential_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:34:11.263991+00:00
-- url     : https://prove2.me/submissions/048a53f3-d328-4d07-872f-ed3040c45de6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LocalSearchFailureReduction

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalSearchFailureReduction
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators
namespace QEC.Coding.BDL26LocalSearchFailureReduction
theorem _root_.solution (S : OddScale) (x : (C S).X) (h : Error S)
    (hh : hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar (C S) x)
    (hb : localSuccess S (delta S h)) :
    boundary S (rawStarPotential S x h hh hb)=h+D S 0+D S (delta S h) :=
  Classical.choose_spec (raw_star_endpoint S x h hh hb)
end QEC.Coding.BDL26LocalSearchFailureReduction

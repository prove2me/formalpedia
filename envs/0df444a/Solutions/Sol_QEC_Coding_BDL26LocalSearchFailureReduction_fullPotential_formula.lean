-- Prove2me | solution 1 for QEC.Coding.BDL26LocalSearchFailureReduction.fullPotential_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:23:21.19896+00:00
-- url     : https://prove2.me/submissions/580b4750-c959-4df0-8a24-d6365567cbff

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
theorem _root_.solution (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0)
    (hb : localSuccess S (secondReadout S n u q)) :
    fullPotential S n u q hs hb=
      intervalMap0 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
        (basePotential S n u q hs hb)+accumulated S n u q := rfl
end QEC.Coding.BDL26LocalSearchFailureReduction

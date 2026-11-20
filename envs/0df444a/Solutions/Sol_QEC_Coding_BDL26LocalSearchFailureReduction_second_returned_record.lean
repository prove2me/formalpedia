-- Prove2me | solution 1 for QEC.Coding.BDL26LocalSearchFailureReduction.second_returned_record
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:25:29.765309+00:00
-- url     : https://prove2.me/submissions/f0607ebf-477a-46d4-8d46-58f5d2034c94

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
    (q : Physical S (n+2)) (hb : localSuccess S (secondReadout S n u q)) :
    ∃ w : Word F (BDL26LevelTwoDecoder.ExecutableQ S),
      localSearch S (secondReadout S n u q)=some w ∧
      D S (secondReadout S n u q)=BDL26LevelTwoDecoder.toActualError S w ∧
      levelTwoLocalError S (D S (secondReadout S n u q)) ∧
      delta S (D S (secondReadout S n u q))=secondReadout S n u q := by
  obtain ⟨w,hw⟩ := hb
  exact ⟨w,hw,returned_record S _ w hw⟩
end QEC.Coding.BDL26LocalSearchFailureReduction

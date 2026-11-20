-- Prove2me | solution 1 for QEC.Coding.BDL26FirstZeroFaceEndpoint.source_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:37:40.45865+00:00
-- url     : https://prove2.me/submissions/616fb7b1-01e0-42e2-907c-1cac8fa3018b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_first_zero_chiX

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstZeroFaceEndpoint
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators
namespace QEC.Coding.BDL26FirstZeroFaceEndpoint
theorem _root_.solution (S : OddScale) (k : Nat) (hk : 1≤k)
    (u : XSyndromeDomain S (2*(k-1))) (q : Physical S (2*(k-1)+2))
    (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S)
    (hs : firstReadout S (2*(k-1)) u=0)
    (hf : terminalFace S (2*(k-1)) u q z f) :
    2*(k-1)+2=2*k ∧ BDL26LogicalDefectProtection.chiX S (2*(k-1)) u q=0 :=
  ⟨by omega,first_zero_chiX S _ u q z f hs hf⟩
end QEC.Coding.BDL26FirstZeroFaceEndpoint

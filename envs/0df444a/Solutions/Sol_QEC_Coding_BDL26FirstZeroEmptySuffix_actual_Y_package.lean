-- Prove2me | solution 1 for QEC.Coding.BDL26FirstZeroEmptySuffix.actual_Y_package
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:00:34.972192+00:00
-- url     : https://prove2.me/submissions/48d56598-8f6c-48fe-93cd-3e9dba23bf31

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroEmptySuffix
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_physical_Y_iXZ
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_actual_Y_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_actual_Y_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_physical_Y_iXZ
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_actual_Y_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_physical_Y_iXZ


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstZeroEmptySuffix
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators
open QEC.Semantics BDL26PairedDecoderPhase
namespace QEC.Coding.BDL26FirstZeroEmptySuffix
theorem _root_.solution (S : OddScale) (s : Visible S 0) (q : Physical S 2)
    (hs : firstReadout S 0 s.1=0) :
    CSSDaviesLocality.coupling q .y=Complex.I • (Qubit.localX q*Qubit.localZ q) ∧
    (BDL26CSSDaviesLocality.coupling S 2 q .y*BDL26PairedDecoderChannel.dressedZ S 0-
      BDL26PairedDecoderChannel.dressedZ S 0*BDL26CSSDaviesLocality.coupling S 2 q .y)*atom S 0 s=0 :=
  ⟨physical_Y_iXZ S q,actual_Y_dressed_Z S s q hs⟩
end QEC.Coding.BDL26FirstZeroEmptySuffix

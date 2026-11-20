-- Prove2me | solution 1 for QEC.Coding.BDL26FirstZeroEmptySuffix.physical_Y_dressed_Z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:35:42.37698+00:00
-- url     : https://prove2.me/submissions/7bd8a0c7-02b9-4092-bdd5-e7b7be5d6239

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroEmptySuffix
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_first_zero_chiX
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_paired_Y_bit
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_first_zero_chiX
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_protected_Z_iff


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
    (toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .y)*BDL26PairedDecoderChannel.dressedZ S 0-
      BDL26PairedDecoderChannel.dressedZ S 0*toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .y))*
      atom S 0 s=0 := by
  apply (BDL26LogicalDefectProtection.protected_Z_iff S 0 s _).mpr
  rw [paired_Y_bit]
  exact first_zero_chiX S s.1 q hs
end QEC.Coding.BDL26FirstZeroEmptySuffix

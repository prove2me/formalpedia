-- Prove2me | solution 1 for QEC.Coding.BDL26FirstZeroEmptySuffix.physical_X_dressed_Z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:35:36.174202+00:00
-- url     : https://prove2.me/submissions/97861cab-0797-4ef9-a0f1-1130a81e0d6d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroEmptySuffix
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_first_zero_chiX
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_paired_X_bit
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
    (toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x)*BDL26PairedDecoderChannel.dressedZ S 0-
      BDL26PairedDecoderChannel.dressedZ S 0*toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x))*
      atom S 0 s=0 := by
  apply (BDL26LogicalDefectProtection.protected_Z_iff S 0 s _).mpr
  rw [paired_X_bit]
  exact first_zero_chiX S s.1 q hs
end QEC.Coding.BDL26FirstZeroEmptySuffix

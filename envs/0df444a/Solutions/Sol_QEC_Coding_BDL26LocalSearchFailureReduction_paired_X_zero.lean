-- Prove2me | solution 1 for QEC.Coding.BDL26LocalSearchFailureReduction.paired_X_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:40:23.662895+00:00
-- url     : https://prove2.me/submissions/ca1a90cd-86fc-4c92-bc7f-ffde1adcae90

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LocalSearchFailureReduction
import Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_successful_chiX_zero
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_paired_X_bit


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
open QEC.Semantics BDL26PairedDecoderPhase
namespace QEC.Coding.BDL26LocalSearchFailureReduction
theorem _root_.solution (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (hs : firstReadout S n s.1=0)
    (hb : localSuccess S (secondReadout S n s.1 q)) :
    BDL26LogicalDefectProtection.dX S n s (CSSDaviesLocality.singlePauli q .x)=0 := by
  rw [paired_X_bit]
  exact successful_chiX_zero S n s.1 q hs hb
end QEC.Coding.BDL26LocalSearchFailureReduction

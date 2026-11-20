-- Prove2me | solution 1 for QEC.Coding.BDL26RXFaceEdgeTower.physical_X_dressed_Z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:29:36.877781+00:00
-- url     : https://prove2.me/submissions/ff4272a0-96dd-4a8f-8bc5-a2e56f46e69f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Theorems.Thm_QEC_Coding_BDL26RXFaceEdgeTower_first_zero_chiX
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_paired_X_bit
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_first_zero_chiX
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_first_zero_chiX
import Theorems.Thm_QEC_Coding_BDL26FirstZeroQVertexTower_first_zero_chiX
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_protected_Z_iff


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFaceEdgeTower
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators
open QEC.Semantics BDL26PairedDecoderPhase
namespace QEC.Coding.BDL26RXFaceEdgeTower
theorem _root_.solution (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n s.1=0) :
    (toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x)*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x))*
      atom S n s=0 := by
  apply (BDL26LogicalDefectProtection.protected_Z_iff S n s _).mpr
  rw [paired_X_bit]
  exact first_zero_chiX S n s.1 q t hs
end QEC.Coding.BDL26RXFaceEdgeTower

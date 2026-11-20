-- Prove2me | solution 1 for QEC.Coding.BDL26BoundaryTailInvariance.physical_potential_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:58:07.962941+00:00
-- url     : https://prove2.me/submissions/4bcc1292-1c72-433e-ac2c-4290a9501ea0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_full_potential_spec
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_full_residual
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundaryTailInvariance
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26TannerLocalRegularity
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26TransposedStoppedDecoder PauliSymplectic
open scoped Classical
namespace QEC.Coding.BDL26BoundaryTailInvariance
theorem _root_.solution (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(snapshot S n u q a).word) :
    (SuffixData S n).family.coboundary0 (TopIndex n) (physicalPotential S n u q a p hp)=
      BDL26LogicalDefectProtection.deltaX S n u q := by
  have h := full_potential_spec S n _ _ (physicalTop S n u q) a p hp
  change (SuffixData S n).family.coboundary0 (TopIndex n) (physicalPotential S n u q a p hp)=
    topWord S n (input S n u) (BDL26ActualFailureReadout.flip S n q) at h
  exact h.trans (BDL26ActualFailureReadout.full_residual S n u q)
end QEC.Coding.BDL26BoundaryTailInvariance

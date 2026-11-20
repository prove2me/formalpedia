-- Prove2me | solution 1 for QEC.Coding.BDL26FirstZeroFaceEndpoint.full_face_potential_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:51:18.383887+00:00
-- url     : https://prove2.me/submissions/60f80e22-4380-4e4e-9ba9-0b894f83d225

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_base_face_potential_spec
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_full_history
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_intervalMap_commutes0
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
theorem _root_.solution (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S)
    (hs : firstReadout S n u=0) (hf : terminalFace S n u q z f) :
    (SuffixData S n).family.coboundary0 (TopIndex n) (fullFacePotential S n u q z f hf)=
      BDL26LogicalDefectProtection.deltaX S n u q := by
  unfold fullFacePotential
  rw [map_add,intervalMap_commutes0 _ n (Nat.le_refl _) 0 (Nat.zero_le _),
    base_face_potential_spec S n u q z f hs hf]
  exact (full_history S n u q).symm
end QEC.Coding.BDL26FirstZeroFaceEndpoint

-- Prove2me | solution 1 for QEC.Coding.BDL26FirstZeroFaceEndpoint.original_correction_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:03:43.461515+00:00
-- url     : https://prove2.me/submissions/6e0f2f98-1eca-4485-ba43-f2addb5a4f57

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_full_face_potential_spec

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
      flip S n q+xCorrection S n u+xCorrection S n (translateX S n u (flip S n q)) := by
  rw [full_face_potential_spec S n u q z f hs hf]
  unfold BDL26LogicalDefectProtection.deltaX BDL26ActualFailureReadout.flip
  ac_rfl
end QEC.Coding.BDL26FirstZeroFaceEndpoint

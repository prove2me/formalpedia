-- Prove2me | solution 1 for QEC.Coding.BDL26FirstZeroFaceEndpoint.face_fillings_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:53:48.927022+00:00
-- url     : https://prove2.me/submissions/5dee7834-a64a-4274-8dc9-30dbca082b5e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint

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
theorem _root_.solution (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : faceSupported S z f h) :
    (∀ q v, boundary S (faceQPotential S z f h hh) (.inr ⟨q,v⟩)=
      faceResidual S h (.inr ⟨q,v⟩)) ∧
    (∀ q v, (faceResidual S h+boundary S (faceQPotential S z f h hh)) (.inr ⟨q,v⟩)=0) ∧
    boundary S (faceZPotential S z f h hh)=faceResidual S h+boundary S (faceQPotential S z f h hh) ∧
    boundary S (faceZPotential S z f h hh+faceQPotential S z f h hh)=faceResidual S h :=
  Classical.choose_spec (Classical.choose_spec (face_full_filling S z f h hh))
end QEC.Coding.BDL26FirstZeroFaceEndpoint

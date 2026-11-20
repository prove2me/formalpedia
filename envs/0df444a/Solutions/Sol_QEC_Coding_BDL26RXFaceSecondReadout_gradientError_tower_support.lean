-- Prove2me | solution 1 for QEC.Coding.BDL26RXFaceSecondReadout.gradientError_tower_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:13:19.932199+00:00
-- url     : https://prove2.me/submissions/b08f0b27-ef4d-4cff-81ff-d2e5a4430857

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceSecondReadout
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xExtend_at_q
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xExtend_other


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFaceSecondReadout
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26RXDecoderAdapter
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXFaceSecondReadout
theorem _root_.solution (z : (RawOne witnessScale).Z)
    (f : ZDoubleCylinderFace (RawOne witnessScale) z witnessScale)
    (g : Word F (DoubleCylinderVertex P
      (BDL26RXFaceEdgeTower.faceOwner witnessScale z f) witnessScale))
    (q : Physical witnessScale 3)
    (hq : q∈hammingSupport
      (gradientError (BDL26RXFaceEdgeTower.faceOwner witnessScale z f) g)) :
    Nonempty (BDL26RXFaceEdgeTower.Tower witnessScale 1 q) := by
  rcases q with ⟨y,e⟩ | ⟨r,v⟩
  · have hy : y=BDL26RXFaceEdgeTower.faceOwner witnessScale z f := by
      by_contra hn
      have hz := xExtend_other P witnessScale
        (BDL26RXFaceEdgeTower.faceOwner witnessScale z f) y hn
        (wordLinearMapTranspose (doubleCylinderBoundary1 P
          (BDL26RXFaceEdgeTower.faceOwner witnessScale z f) witnessScale) g) e
      exact (Finset.mem_filter.mp hq).2 hz
    subst y
    have he : BDL26RXFaceEdgeTower.seedPhysical witnessScale ⟨z,f,e⟩=
        Sum.inl ⟨BDL26RXFaceEdgeTower.faceOwner witnessScale z f,e⟩ := rfl
    rw [←he]
    exact ⟨BDL26RXFaceEdgeTower.Tower.seed ⟨z,f,e⟩⟩
  · have hz := xExtend_at_q P witnessScale
      (BDL26RXFaceEdgeTower.faceOwner witnessScale z f)
      (wordLinearMapTranspose (doubleCylinderBoundary1 P
        (BDL26RXFaceEdgeTower.faceOwner witnessScale z f) witnessScale) g) r v
    exact False.elim ((Finset.mem_filter.mp hq).2 hz)
end QEC.Coding.BDL26RXFaceSecondReadout

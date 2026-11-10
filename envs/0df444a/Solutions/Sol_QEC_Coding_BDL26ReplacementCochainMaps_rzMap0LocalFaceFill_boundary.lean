-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementCochainMaps.rzMap0LocalFaceFill_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:09:39.14898+00:00
-- url     : https://prove2.me/submissions/26749892-5f6a-47a1-b5e9-9eb55ac59f75

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_doubleCylinderBoundary2_extendCopyZero
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzCoboundary0_extendRZFaceWord

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementCochainMaps
open scoped BigOperators Classical
open QEC.Coding
open QEC.Coding.BDL26FiniteTannerSquare
open QEC.Coding.BDL26TannerLocalRegularity
open QEC.Coding.BDL26RXLocalReplacement
open QEC.Coding.BDL26RZLocalReplacement
open QEC.Coding.BDL26RZMap1CoordinateBridge
open QEC.Coding.MultiscaleDecoder
namespace QEC.Coding.BDL26ReplacementCochainMaps
theorem _root_.solution
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (z : P.Z) :
    rzCoboundary0 P A4 S (rzMap0LocalFaceFill P S x z) =
      ∑ owner : RZOldFaceOver P x z,
        extendRZLocalEdgeWord P S z
          (extendCopyZeroSubdivisionEdgeWord (transposePresentation P) z S
            (subdivisionBoundary2 (transposePresentation P) z S
              (subdivisionWholeFaceChain (transposePresentation P) z S
                (rzOldFaceOverZStarFace P x z owner)))) := by
  classical
  unfold rzMap0LocalFaceFill
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro owner _
  erw [rzCoboundary0_extendRZFaceWord, doubleCylinderBoundary2_extendCopyZero]
end QEC.Coding.BDL26ReplacementCochainMaps

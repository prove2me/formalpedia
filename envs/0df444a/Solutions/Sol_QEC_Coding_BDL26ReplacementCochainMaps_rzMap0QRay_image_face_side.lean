-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementCochainMaps.rzMap0QRay_image_face_side
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:04:56.934108+00:00
-- url     : https://prove2.me/submissions/6697d93a-0b06-441f-9635-212f5950dabc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) (z : P.Z)
    (owner : RZOldFaceOver P x z) (corner : Two)
    (hxq : P.xq x (P.faceQ owner.1 corner) = true)
    (hqz : P.qz (P.faceQ owner.1 corner) z = true) :
    rzQZDegreeZero P A (P.faceQ owner.1 corner) z hqz S
        (rzMap0QRay P S x (P.faceQ owner.1 corner) hxq) =
      ∑ i : Fin S.half, canonicalBasisWord
        (Sum.inl (0, Sum.inl
          (xStarFaceQZEdge (transposePresentation P) z
            (rzOldFaceOverZStarFace P x z owner) corner, i)) :
          ZDoubleCylinderEdge P z S) := by
  classical
  unfold rzQZDegreeZero rzMap0QRay
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [wordPushforward_canonicalBasis]
  congr 1
  apply congrArg Sum.inl
  change (0, Sum.inl _) = (0, Sum.inl _)
  congr 2
  change (_, i) = (_, i)
  congr 1
  apply Subtype.ext
  apply congrArg Sum.inr
  apply Subtype.ext
  change (P.faceQ owner.1 corner, x) = (P.faceQ owner.1 corner, P.faceX owner.1)
  exact Prod.ext rfl owner.2.1.symm
end QEC.Coding.BDL26ReplacementCochainMaps

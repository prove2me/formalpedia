-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.rxCxCocycle_faceXCorner_eq_boundaryRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:45:34.405906+00:00
-- url     : https://prove2.me/submissions/5538867e-00b5-4cb4-a5bc-0aeeb75f4af2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCxCocycle_eq_on_starEdge
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCxCocycle_eq_on_boundaryVertex
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
universe u
namespace QEC.Coding.BDL26RXLocalReplacement
theorem _root_.solution
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (copy : Two) (face : XStarFace P x)
    (word : Word Field (DoubleCylinderVertex P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary1 word = 0) :
    word (copy, Sum.inl (xStarFaceXVertex P x face)) =
      word (copy,
        (subdivisionOriginalBoundaryVertex P x S (A.xBoundaryRoot x)).1) := by
  let boundaryQ : XStarBoundaryVertex P x :=
    ⟨Vertex.q (P.faceQ face.1 0), by
      change decide (∃ candidate : P.Face,
        xStarFaceMember P x candidate = true ∧
          (P.faceQ face.1 0 = P.faceQ candidate 0 ∨
            P.faceQ face.1 0 = P.faceQ candidate 1)) = true
      rw [decide_eq_true_eq]
      exact ⟨face.1, face.2, Or.inl rfl⟩⟩
  have hedge := rxCxCocycle_eq_on_starEdge P x S copy
    (xStarFaceXQEdge P x face 0) word hword
  have hq : Sum.inl (xStarFaceQVertex P x face 0) =
      (subdivisionOriginalBoundaryVertex P x S boundaryQ).1 := by
    apply congrArg Sum.inl
    apply Subtype.ext
    rfl
  rw [xStarEdgeStart_faceXQEdge, xStarEdgeEnd_faceXQEdge, hq] at hedge
  exact hedge.symm.trans
    (rxCxCocycle_eq_on_boundaryVertex P A x S copy word hword boundaryQ)
end QEC.Coding.BDL26RXLocalReplacement

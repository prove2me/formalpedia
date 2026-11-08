-- Prove2me | solution 1 for QEC.Coding.BDL26RZLocalReplacement.faceQ_zero_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:44:44.113361+00:00
-- url     : https://prove2.me/submissions/5546fee7-a9fc-423b-9761-d09a6c57af7d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
namespace QEC.Coding.BDL26RZLocalReplacement
theorem _root_.solution (P : TannerSquarePresentation) (face : P.Face) :
    P.faceQ face 0 ≠ P.faceQ face 1 := by
  intro hq
  let first : FaceOver P.data (P.faceX face) (P.faceZ face) × Two :=
    (⟨face, rfl, rfl⟩, 0)
  let second : FaceOver P.data (P.faceX face) (P.faceZ face) × Two :=
    (⟨face, rfl, rfl⟩, 1)
  have hshared : faceCornerToShared P.data (P.faceX face) (P.faceZ face) first =
      faceCornerToShared P.data (P.faceX face) (P.faceZ face) second := by
    apply Subtype.ext
    exact hq
  have hcorners := (P.perfectPairing (P.faceX face) (P.faceZ face)).1 hshared
  have hbits := congrArg (fun corner => corner.2.1) hcorners
  norm_num [first, second] at hbits
end QEC.Coding.BDL26RZLocalReplacement

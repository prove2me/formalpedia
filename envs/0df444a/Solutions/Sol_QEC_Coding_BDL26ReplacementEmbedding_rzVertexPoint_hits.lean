-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rzVertexPoint_hits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:42:18.207984+00:00
-- url     : https://prove2.me/submissions/3266dbba-4fcf-4240-8dfe-8db08f4a6575

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rzVertexPoint_faceImage
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_familyHits_congr_fintype

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) (region : Set E) :
    familyHits (tannerFaceImage (BDL26RZLocalReplacement.rzReplacementPresentation P A S)
      (rzVertexPoint P A S J)) region = familyHits (rzFaceImage P A S J) region := by
  exact familyHits_congr_fintype
    (BDL26RZLocalReplacement.rzReplacementPresentation P A S).data.faceFintype
    (inferInstance : Fintype (BDL26RZLocalReplacement.RZFace P S))
    _ _ (rzVertexPoint_faceImage P A S J) region
end QEC.Coding.BDL26ReplacementEmbedding

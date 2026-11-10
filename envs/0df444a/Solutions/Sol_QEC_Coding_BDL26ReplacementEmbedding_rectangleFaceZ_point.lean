-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rectangleFaceZ_point
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:27:26.473324+00:00
-- url     : https://prove2.me/submissions/baeb81a1-e036-4f2d-ab9f-eaeb1d42b0d7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (edge : SubdivisionBoundaryEdge P x S)
    (copy endpoint : BDL26FiniteTannerSquare.Two) :
    rxTwoPoint P S J (localFaceZ P S ⟨x, .inr edge, copy, endpoint⟩) =
      rectangleMidpoint P S J x edge := rfl
end QEC.Coding.BDL26ReplacementEmbedding

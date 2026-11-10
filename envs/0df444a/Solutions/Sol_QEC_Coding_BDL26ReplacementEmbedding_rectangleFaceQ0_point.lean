-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rectangleFaceQ0_point
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:27:15.549729+00:00
-- url     : https://prove2.me/submissions/8e7b39fe-7606-4d4b-8892-82acd7bc7bab

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
    rxOnePoint P S J (localFaceQ0 P S ⟨x, .inr edge, copy, endpoint⟩) =
      rectangleMidpoint P S J x edge := rfl
end QEC.Coding.BDL26ReplacementEmbedding

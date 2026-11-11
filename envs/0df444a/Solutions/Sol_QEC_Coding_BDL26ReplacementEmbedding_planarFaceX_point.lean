-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.planarFaceX_point
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:02:13.330163+00:00
-- url     : https://prove2.me/submissions/5e6886b5-c0ff-48d2-b3ec-81a97fd9e09b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_subdivisionVertexPoint_grid

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (f : XStarFace P x) (i j : Fin S.half)
    (copy a b : BDL26FiniteTannerSquare.Two) :
    rxZeroPoint P S J (localFaceX P S ⟨x, .inl (copy, f, i, j), a, b⟩) =
      facePoint P J f.1 (2 * ((gridEndpoint i a).val : ℝ) / S.ell)
        (2 * ((gridEndpoint j b).val : ℝ) / S.ell) :=
  subdivisionVertexPoint_grid P S J x f (gridEndpoint i a) (gridEndpoint j b)
end QEC.Coding.BDL26ReplacementEmbedding

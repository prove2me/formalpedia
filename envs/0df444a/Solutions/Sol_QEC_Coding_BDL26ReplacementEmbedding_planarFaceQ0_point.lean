-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.planarFaceQ0_point
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:06:50.889832+00:00
-- url     : https://prove2.me/submissions/97702c3c-a549-4c9a-a04d-fb1816dfab17

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_subdivisionHorizontalEdge_midpoint

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
    rxOnePoint P S J (localFaceQ0 P S ⟨x, .inl (copy, f, i, j), a, b⟩) =
      facePoint P J f.1 ((2 * (i.val : ℝ) + 1) / S.ell)
        (2 * ((gridEndpoint j b).val : ℝ) / S.ell) := by
  have hb : subdivisionFaceBoundaryEdge P x S (f, i, j) (0, b) =
      subdivisionHorizontalEdge P x S f i (gridEndpoint j b) := by
    fin_cases b <;> rfl
  change (1 / 2 : ℝ) •
    (subdivisionVertexPoint P S J x
      (subdivisionEdgeStart P x S (subdivisionFaceBoundaryEdge P x S (f, i, j) (0, b))) +
     subdivisionVertexPoint P S J x
      (subdivisionEdgeEnd P x S (subdivisionFaceBoundaryEdge P x S (f, i, j) (0, b)))) = _
  rw [hb]
  exact subdivisionHorizontalEdge_midpoint P S J x f i (gridEndpoint j b)
end QEC.Coding.BDL26ReplacementEmbedding

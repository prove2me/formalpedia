-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.planarFaceQ1_point
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:06:54.301447+00:00
-- url     : https://prove2.me/submissions/dd419d1e-018f-43bd-abdf-26a4d416bbba

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_subdivisionVerticalEdge_midpoint

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
    rxOnePoint P S J (localFaceQ1 P S ⟨x, .inl (copy, f, i, j), a, b⟩) =
      facePoint P J f.1 (2 * ((gridEndpoint i a).val : ℝ) / S.ell)
        ((2 * (j.val : ℝ) + 1) / S.ell) := by
  have hb : subdivisionFaceBoundaryEdge P x S (f, i, j) (1, a) =
      subdivisionVerticalEdge P x S f (gridEndpoint i a) j := by
    fin_cases a <;> rfl
  change (1 / 2 : ℝ) •
    (subdivisionVertexPoint P S J x
      (subdivisionEdgeStart P x S (subdivisionFaceBoundaryEdge P x S (f, i, j) (1, a))) +
     subdivisionVertexPoint P S J x
      (subdivisionEdgeEnd P x S (subdivisionFaceBoundaryEdge P x S (f, i, j) (1, a)))) = _
  rw [hb]
  exact subdivisionVerticalEdge_midpoint P S J x f (gridEndpoint i a) j
end QEC.Coding.BDL26ReplacementEmbedding

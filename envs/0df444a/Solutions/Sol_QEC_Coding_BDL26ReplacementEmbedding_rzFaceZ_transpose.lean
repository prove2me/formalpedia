-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rzFaceZ_transpose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:58:44.553614+00:00
-- url     : https://prove2.me/submissions/89bb793f-01b8-4249-bb71-51b3b02aaa35

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_qToZDoubleCylinderVertex_eq_raw

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (f : BDL26RZLocalReplacement.RZFace P S) :
    BDL26RZLocalReplacement.rzFaceZ P A S f =
      rxFaceX (transposePresentation P) S (rzFaceEquiv P S f) := by
  rcases f with ⟨z, cell, a, b⟩ | ⟨⟨⟨q, z⟩, hqz⟩, edge, endpoint⟩ | ⟨old, copy⟩
  · rcases cell with ⟨copy, f, i, j⟩ | boundary
    · fin_cases a <;> fin_cases b <;> rfl
    · fin_cases a <;> fin_cases b <;> rfl
  · let root := qDoubleCylinderUnderlyingStarEdge (transposePresentation P) q S edge
    fin_cases endpoint
    · change (⟨z, qToZDoubleCylinderVertex P A q z hqz S
          (qDoubleCylinderEdgeStart (transposePresentation P) q S edge)⟩ :
          BDL26RZLocalReplacement.RZZ P S) = _
      rw [qToZDoubleCylinderVertex_eq_raw P A S q z hqz root]
      exact congrArg (fun v : DoubleCylinderVertex (transposePresentation P) z S =>
        (⟨z, v⟩ : BDL26RZLocalReplacement.RZZ P S))
        (qToXDoubleCylinderEdgeRaw_start (transposePresentation P) q z hqz S root edge)
    · change (⟨z, qToZDoubleCylinderVertex P A q z hqz S
          (qDoubleCylinderEdgeEnd (transposePresentation P) q S edge)⟩ :
          BDL26RZLocalReplacement.RZZ P S) = _
      rw [qToZDoubleCylinderVertex_eq_raw P A S q z hqz root]
      exact congrArg (fun v : DoubleCylinderVertex (transposePresentation P) z S =>
        (⟨z, v⟩ : BDL26RZLocalReplacement.RZZ P S))
        (qToXDoubleCylinderEdgeRaw_end (transposePresentation P) q z hqz S root edge)
  · rfl
end QEC.Coding.BDL26ReplacementEmbedding

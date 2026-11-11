-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rzFaceQ_transpose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:57:36.478881+00:00
-- url     : https://prove2.me/submissions/ec2381d0-ef80-4b71-bfd5-7c88a54071f3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_qToZDoubleCylinderEdge_eq_raw

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (f : BDL26RZLocalReplacement.RZFace P S)
    (corner : BDL26FiniteTannerSquare.Two) :
    BDL26RZLocalReplacement.rzFaceQ P A S f corner =
      rxFaceQ (transposePresentation P) S (rzFaceEquiv P S f) corner := by
  rcases f with ⟨z, cell, a, b⟩ | ⟨⟨⟨q, z⟩, hqz⟩, edge, endpoint⟩ | ⟨old, copy⟩
  · rcases cell with ⟨copy, f, i, j⟩ | boundary
    · fin_cases corner <;> fin_cases a <;> fin_cases b <;> rfl
    · fin_cases corner <;> fin_cases a <;> fin_cases b <;> rfl
  · fin_cases corner
    · change (Sum.inl ⟨z, qToZDoubleCylinderEdge P A q z hqz S edge⟩ :
          BDL26RZLocalReplacement.RZQ P S) = _
      rw [qToZDoubleCylinderEdge_eq_raw]
      rfl
    · rfl
  · rfl
end QEC.Coding.BDL26ReplacementEmbedding

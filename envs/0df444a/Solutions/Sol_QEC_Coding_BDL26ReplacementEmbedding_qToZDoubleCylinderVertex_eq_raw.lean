-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.qToZDoubleCylinderVertex_eq_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:54:26.244199+00:00
-- url     : https://prove2.me/submissions/c6468216-84a3-44ab-aa53-d94cd053fdda

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
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q) (z : P.Z)
    (hqz : P.qz q z = true) (root : QStarEdge (transposePresentation P) q)
    (v : QDoubleCylinderVertex (transposePresentation P) q S) :
    qToZDoubleCylinderVertex P A q z hqz S v =
      qToXDoubleCylinderVertexAtRoot (transposePresentation P) q z hqz S root v := by
  rcases v with ⟨copy, (u | edge) | ⟨edge, i⟩⟩ <;> rfl
end QEC.Coding.BDL26ReplacementEmbedding

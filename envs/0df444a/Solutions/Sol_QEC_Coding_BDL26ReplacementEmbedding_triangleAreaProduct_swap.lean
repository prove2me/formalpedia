-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.triangleAreaProduct_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:22:46.942288+00:00
-- url     : https://prove2.me/submissions/7a7c75a8-de3c-492e-bdf2-8bb8e83daeea

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_triangleAreaProduct_sq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (b c : E) :
    triangleAreaProduct b c = triangleAreaProduct c b := by
  have hsq : triangleAreaProduct b c ^ 2 = triangleAreaProduct c b ^ 2 := by
    rw [triangleAreaProduct_sq, triangleAreaProduct_sq, real_inner_comm c b]
    ring
  have hb : 0 ≤ triangleAreaProduct b c := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hc : 0 ≤ triangleAreaProduct c b := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith
end QEC.Coding.BDL26ReplacementEmbedding

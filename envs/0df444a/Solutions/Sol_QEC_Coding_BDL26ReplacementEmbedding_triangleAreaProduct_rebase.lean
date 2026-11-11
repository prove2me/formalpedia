-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.triangleAreaProduct_rebase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:22:50.268304+00:00
-- url     : https://prove2.me/submissions/b7bbff7f-d0a8-4602-9e2b-561a3dcab586

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
    triangleAreaProduct b c = triangleAreaProduct (c - b) (-b) := by
  have hsq : triangleAreaProduct b c ^ 2 = triangleAreaProduct (c - b) (-b) ^ 2 := by
    rw [triangleAreaProduct_sq, triangleAreaProduct_sq, norm_sub_sq_real, norm_neg,
      inner_neg_right, inner_sub_left, real_inner_self_eq_norm_sq,
      real_inner_comm c b]
    ring
  have hb : 0 ≤ triangleAreaProduct b c := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hc : 0 ≤ triangleAreaProduct (c - b) (-b) := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith
end QEC.Coding.BDL26ReplacementEmbedding

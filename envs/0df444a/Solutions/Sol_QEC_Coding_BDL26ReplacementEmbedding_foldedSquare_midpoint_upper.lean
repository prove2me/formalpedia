-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.foldedSquare_midpoint_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:29:54.901141+00:00
-- url     : https://prove2.me/submissions/c43648ed-3bef-4a0e-9e73-23e59beb38e6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_foldedSquare_of_u_le_v

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (x q₀ q₁ z : E) {u₀ v₀ u₁ v₁ : ℝ}
    (h₀ : u₀ ≤ v₀) (h₁ : u₁ ≤ v₁) :
    (1 / 2 : ℝ) • (foldedSquare x q₀ q₁ z u₀ v₀ + foldedSquare x q₀ q₁ z u₁ v₁) =
      foldedSquare x q₀ q₁ z ((u₀ + u₁) / 2) ((v₀ + v₁) / 2) := by
  have hm : (u₀ + u₁) / 2 ≤ (v₀ + v₁) / 2 := by linarith
  rw [foldedSquare_of_u_le_v x q₀ q₁ z h₀,
    foldedSquare_of_u_le_v x q₀ q₁ z h₁, foldedSquare_of_u_le_v x q₀ q₁ z hm]
  module
end QEC.Coding.BDL26ReplacementEmbedding

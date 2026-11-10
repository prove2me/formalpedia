-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.triangleUnitDirection_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:32:18.612816+00:00
-- url     : https://prove2.me/submissions/49aaad78-dd4c-4ca0-ba28-5d75b1649c2c

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution {b : E} (hb : b ≠ 0) :
    ⟪triangleUnitDirection b, b⟫_ℝ = ‖b‖ := by
  rw [triangleUnitDirection, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hn : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  field_simp [hn]
end QEC.Coding.BDL26ReplacementEmbedding

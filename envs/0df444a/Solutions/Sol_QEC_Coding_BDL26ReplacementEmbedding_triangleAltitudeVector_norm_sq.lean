-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.triangleAltitudeVector_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:12:43.788065+00:00
-- url     : https://prove2.me/submissions/0f05b056-8044-4fc2-b04f-95350653065a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_triangleUnitDirection_norm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution {b c : E} (hb : b ≠ 0) :
    ‖triangleAltitudeVector b c‖ ^ 2 =
      ‖c‖ ^ 2 - ⟪triangleUnitDirection b, c⟫_ℝ ^ 2 := by
  rw [triangleAltitudeVector, norm_sub_sq_real, real_inner_smul_right,
    norm_smul, Real.norm_eq_abs, triangleUnitDirection_norm hb, mul_one,
    sq_abs, real_inner_comm c (triangleUnitDirection b)]
  ring
end QEC.Coding.BDL26ReplacementEmbedding

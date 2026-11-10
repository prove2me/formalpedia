-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.BoundaryUnit.swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:40:39.69933+00:00
-- url     : https://prove2.me/submissions/87c21624-d5ba-4688-9e22-b3e42cae29eb

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
namespace BoundaryUnit
theorem _root_.solution {x q₀ q₁ z : E} (h : BoundaryUnit x q₀ q₁ z) :
    BoundaryUnit x q₁ q₀ z := ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩
end BoundaryUnit
end QEC.Coding.BDL26ReplacementEmbedding

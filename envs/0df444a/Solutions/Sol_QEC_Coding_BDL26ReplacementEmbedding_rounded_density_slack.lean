-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rounded_density_slack
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:47:04.685473+00:00
-- url     : https://prove2.me/submissions/0b0b8b22-1e96-412e-bb74-25e567db3a83

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open BDL26FiniteTannerSquare
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution {L ell : ℝ} (hL : 13 ≤ L)
    (hell : 0 ≤ ell) (hround : ell ≤ L + 2) :
    48 * ell ^ 2 ≤ 64 * L ^ 2 := by
  have hsquare : ell ^ 2 ≤ (L + 2) ^ 2 := by nlinarith
  have hproduct : 0 ≤ (L - 13) * (L + 1) := mul_nonneg (by linarith) (by linarith)
  nlinarith
end QEC.Coding.BDL26ReplacementEmbedding

-- Prove2me | solution 2 for QEC.Coding.BDL26ReplacementEmbedding.rounded_density_handoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:56:20.959287+00:00
-- url     : https://prove2.me/submissions/a89c6f5d-bcc9-4dad-bf21-8c14da601866

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rounded_density_slack

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open BDL26FiniteTannerSquare
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution {L ell coefficient : ℝ}
    (hL : 13 ≤ L) (hell : 0 ≤ ell) (hround : ell ≤ L + 2)
    (hcoefficient : 0 ≤ coefficient) :
    48 * coefficient * ell ^ 2 ≤ 64 * coefficient * L ^ 2 := by
  have h := mul_le_mul_of_nonneg_left
    (rounded_density_slack hL hell hround) hcoefficient
  nlinarith
end QEC.Coding.BDL26ReplacementEmbedding

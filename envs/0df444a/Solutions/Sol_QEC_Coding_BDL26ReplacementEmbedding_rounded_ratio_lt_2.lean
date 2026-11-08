-- Prove2me | solution 2 for QEC.Coding.BDL26ReplacementEmbedding.rounded_ratio_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:55:51.504192+00:00
-- url     : https://prove2.me/submissions/cfe3b98a-b95c-442d-92d1-30989ff2c737

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
theorem _root_.solution {A lam ell : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    (hround : A * lam < ell) : lam / ell < 1 / A := by
  have hell : 0 < ell := lt_trans (mul_pos hA hlam) hround
  apply (div_lt_div_iff₀ hell hA).2
  nlinarith
end QEC.Coding.BDL26ReplacementEmbedding

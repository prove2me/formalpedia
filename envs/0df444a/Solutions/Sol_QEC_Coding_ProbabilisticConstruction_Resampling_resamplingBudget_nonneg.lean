-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.resamplingBudget_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:21:38.653749+00:00
-- url     : https://prove2.me/submissions/058f4a96-44b8-4466-a8c8-2f3a24a94731

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open scoped BigOperators
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i < 1) (i : I) : 0 ≤ resamplingBudget x i :=
  div_nonneg (hx0 i) (sub_pos.mpr (hx1 i)).le
end QEC.Coding.ProbabilisticConstruction.Resampling

-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.one_add_budget_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:45:27.570908+00:00
-- url     : https://prove2.me/submissions/22ec6dd5-1def-494b-9c66-d4b14a94ae3e

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
theorem _root_.solution (x : I → ℝ) (hx1 : ∀ i, x i < 1) (i : I) :
    (1 + resamplingBudget x i) * (1 - x i) = 1 := by
  unfold resamplingBudget
  field_simp [(sub_pos.mpr (hx1 i)).ne']
  ring
end QEC.Coding.ProbabilisticConstruction.Resampling

-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:46:21.706661+00:00
-- url     : https://prove2.me/submissions/8558a012-1c3c-461a-be15-9014249b3cfb

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessWeight_nonneg

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open scoped BigOperators
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (p : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    (h : ℕ) (i : I) : 0 ≤ witnessPartition G p h i :=
  Finset.sum_nonneg (fun t _ => witnessWeight_nonneg G p hp h i t)
end QEC.Coding.ProbabilisticConstruction.Resampling

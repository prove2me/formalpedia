-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.mem_closedNeighbors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:10:16.527319+00:00
-- url     : https://prove2.me/submissions/84cef1ed-fa08-435b-85d2-952f470b3a95

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open scoped BigOperators
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (i j : I) :
    j ∈ closedNeighbors G i ↔ j = i ∨ G.Adj i j := by
  simp [closedNeighbors]
end QEC.Coding.ProbabilisticConstruction.Resampling

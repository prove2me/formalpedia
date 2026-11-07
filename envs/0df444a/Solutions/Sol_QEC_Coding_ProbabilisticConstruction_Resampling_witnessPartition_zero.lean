-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:09:12.338216+00:00
-- url     : https://prove2.me/submissions/25f60dfb-4757-46ba-af5c-4b932abef945

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
theorem _root_.solution (p : I → ℝ) (i : I) :
    witnessPartition G p 0 i = 0 := by
  unfold witnessPartition
  apply Finset.sum_eq_zero
  intro t ht
  exact PEmpty.elim t
end QEC.Coding.ProbabilisticConstruction.Resampling

-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.fullRowRank_failureMass_le_exact_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:23:10.377933+00:00
-- url     : https://prove2.me/submissions/0ffac21d-9099-4c6e-8984-9a79710767a3

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_failureMass_le_sum_eventMass
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_subsetRowCombination_zero_eventMass
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_exists_nonempty_subsetRowCombination_eq_zero_of_not_fullRowRank

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
universe u
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (@HasFullRowRank r) ≤
      ∑ A : {A : Finset (Fin (3 * r)) // A.Nonempty},
        (ENNReal.ofReal
          ((1 +
            (1 - 2 * (incidenceProbability (4 * r) Delta).toReal) ^
              A.1.card) / 2)) ^ (4 * r) := by
  calc
    _ ≤ ∑ A : {A : Finset (Fin (3 * r)) // A.Nonempty},
        eventMass
          (distribution r Delta hDelta)
          (fun sample => subsetRowCombination sample A.1 = 0) := by
      apply failureMass_le_sum_eventMass
      intro sample hsample
      rcases
          exists_nonempty_subsetRowCombination_eq_zero_of_not_fullRowRank
            hsample with
        ⟨A, hA, hzero⟩
      exact ⟨⟨A, hA⟩, hzero⟩
    _ = _ := by
      apply Fintype.sum_congr
      intro A
      exact subsetRowCombination_zero_eventMass r Delta hDelta A.1
end QEC.Coding.FiberBundle.RandomBase

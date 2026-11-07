-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.subsetRowCombination_zero_eventMass_small_geometric_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:23:06.849624+00:00
-- url     : https://prove2.me/submissions/1d7a6e64-104e-4390-8619-a59f0d6c19a8

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_subsetRowCombination_zero_eventMass_small_le
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_check_expected_degree


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
universe u
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r)
    (A : Finset (Fin (3 * r))) (hsmall : A.card * Delta ≤ 4 * r) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => subsetRowCombination sample A = 0) ≤
      (ENNReal.ofReal (Real.exp (-(Delta : Real) / 2))) ^ A.card := by
  let p : Real := (incidenceProbability (4 * r) Delta).toReal
  have hmean : ((4 * r : Nat) : Real) * p = Delta := by
    exact check_expected_degree r Delta hr
  calc
    _ ≤
        (ENNReal.ofReal
          (Real.exp (-(p * A.card) / 2))) ^ (4 * r) :=
      subsetRowCombination_zero_eventMass_small_le
        r Delta hr hDelta hHalf A hsmall
    _ = ENNReal.ofReal
        ((Real.exp (-(p * A.card) / 2)) ^ (4 * r)) := by
      rw [ENNReal.ofReal_pow (Real.exp_pos _).le]
    _ = ENNReal.ofReal
        ((Real.exp (-(Delta : Real) / 2)) ^ A.card) := by
      congr 1
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      congr 1
      nlinarith
    _ = _ := ENNReal.ofReal_pow (Real.exp_pos _).le A.card
end QEC.Coding.FiberBundle.RandomBase

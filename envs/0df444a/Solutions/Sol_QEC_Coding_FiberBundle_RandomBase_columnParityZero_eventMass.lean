-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.columnParityZero_eventMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:09:38.623375+00:00
-- url     : https://prove2.me/submissions/cb8fe5ae-7697-41ed-9fd5-4d70e6b9a003

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnParityZero_measureReal
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_eventMass_eq_toMeasure


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
universe u
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (A : Finset (Fin (3 * r))) :
    eventMass
        (columnDistribution r Delta hDelta)
        (ColumnParityZero A) =
      ENNReal.ofReal
        ((1 +
          (1 - 2 * (incidenceProbability (4 * r) Delta).toReal) ^ A.card) / 2) := by
  classical
  calc
    _ = (columnDistribution r Delta hDelta).toMeasure
        {column | ColumnParityZero A column} :=
      eventMass_eq_toMeasure _ _
    _ = ENNReal.ofReal
        ((columnDistribution r Delta hDelta).toMeasure.real
          {column | ColumnParityZero A column}) := by
      rw [ofReal_measureReal]
    _ = _ := by rw [columnParityZero_measureReal r Delta hDelta A]
end QEC.Coding.FiberBundle.RandomBase

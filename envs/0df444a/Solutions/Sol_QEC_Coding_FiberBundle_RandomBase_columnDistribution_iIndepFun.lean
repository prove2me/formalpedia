-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.columnDistribution_iIndepFun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:30:00.482899+00:00
-- url     : https://prove2.me/submissions/6ad582cd-8911-4d49-8f03-a24e550f85e1

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_iIndepFun


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
universe u
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ProbabilityTheory.iIndepFun
      (fun a (column : ColumnSample r) => column a)
      (columnDistribution r Delta hDelta).toMeasure := by
  exact independentProduct_iIndepFun _
end QEC.Coding.FiberBundle.RandomBase

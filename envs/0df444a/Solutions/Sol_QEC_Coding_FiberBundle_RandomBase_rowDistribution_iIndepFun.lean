-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.rowDistribution_iIndepFun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:03:07.934018+00:00
-- url     : https://prove2.me/submissions/c4659651-f8b6-45e5-9234-a3150d7c00f5

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_iIndepFun


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ProbabilityTheory.iIndepFun
      (fun b (row : RowSample r) => row b)
      (rowDistribution r Delta hDelta).toMeasure := by
  exact independentProduct_iIndepFun _
end QEC.Coding.FiberBundle.RandomBase

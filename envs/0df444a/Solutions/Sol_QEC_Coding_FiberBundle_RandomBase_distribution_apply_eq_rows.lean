-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.distribution_apply_eq_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:00:43.088986+00:00
-- url     : https://prove2.me/submissions/2b6b41ab-224e-41e7-83c7-828926926ee4

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.distribution_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (sample : Sample r) :
    distribution r Delta hDelta sample =
      rowGroupedDistribution r Delta hDelta (sampleEquivRows r sample) := by
  rw [distribution_apply, rowGroupedDistribution_apply]
  norm_cast
  rw [← Finset.prod_product' Finset.univ Finset.univ]
  rfl
end QEC.Coding.FiberBundle.RandomBase

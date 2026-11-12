-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.denseRange_baseNormOneOrderUnitsToCompleted_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:51:43.520626+00:00
-- url     : https://prove2.me/submissions/f3e889c4-ca40-4003-949a-fe077a380bee

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_NormOneCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_IntrinsicStrongApproximation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_range_baseNormOneOrderUnitsToCompleted

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped PowerSeries.WithPiTopology
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopologicalSpace
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    DenseRange (baseNormOneOrderUnitsToCompleted P r level) ↔
      DenseRange (orderNormOneInnerFormToCompleted P r level) := by
  change Dense (Set.range (baseNormOneOrderUnitsToCompleted P r level)) ↔
    Dense (Set.range (orderNormOneInnerFormToCompleted P r level))
  rw [range_baseNormOneOrderUnitsToCompleted]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger

-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.baseNormOneOrderUnitsReduction_factor_completed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:12:40.023679+00:00
-- url     : https://prove2.me/submissions/74313c51-b818-4553-a6f9-6bb85d113f21

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_NormOneCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_IntrinsicStrongApproximation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderNormOneInnerFormReduction_factor_completed


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped PowerSeries.WithPiTopology
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopologicalSpace
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : CartwrightStegerBaseNormOneOrderUnits P r) :
    baseNormOneOrderUnitsReduction P r level u =
      specialLinearToPSL P r level
        (indexCompletedNormOneReduction P r level
          (baseNormOneOrderUnitsToCompleted P r level u)) := by
  exact orderNormOneInnerFormReduction_factor_completed P r level
    ((orderNormOneInnerFormEquivBaseNormOneOrderUnits P r).symm u)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger

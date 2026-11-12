-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.baseNormOneOrderUnitsReduction_surjective_iff_PSL_le_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:22:42.028991+00:00
-- url     : https://prove2.me/submissions/982703eb-507d-4b2f-9a4a-aa2088495e5c

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_NormOneCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_IntrinsicStrongApproximation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_baseNormOneOrderUnitsReduction_surjective_iff
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderNormOneInnerFormReduction_surjective_iff_PSL_le_image

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped PowerSeries.WithPiTopology
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopologicalSpace
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (baseNormOneOrderUnitsReduction P r level) ↔
      PSL P r level ≤ IndexCartwrightStegerImage P r level := by
  rw [baseNormOneOrderUnitsReduction_surjective_iff,
    orderNormOneInnerFormReduction_surjective_iff_PSL_le_image]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger

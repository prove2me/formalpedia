-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOneInnerFormReduction_surjective_iff_PSL_le_ambient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:15:40.979594+00:00
-- url     : https://prove2.me/submissions/f1f6e932-0449-4143-b5ed-7e8043419aa4

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_NormOneCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_IntrinsicStrongApproximation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderNormOneInnerFormReduction_surjective_iff_PSL_le_innerFormImage

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped PowerSeries.WithPiTopology
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopologicalSpace
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (orderNormOneInnerFormReduction P r level) ↔
      PSL P r level ≤ IndexCartwrightStegerAmbient P r level := by
  rw [orderNormOneInnerFormReduction_surjective_iff_PSL_le_innerFormImage,
    IndexInnerFormImage_eq_IndexCartwrightStegerAmbient]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger

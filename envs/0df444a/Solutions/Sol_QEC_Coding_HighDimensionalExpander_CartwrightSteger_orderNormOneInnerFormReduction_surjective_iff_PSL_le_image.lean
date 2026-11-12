-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOneInnerFormReduction_surjective_iff_PSL_le_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:19:16.073711+00:00
-- url     : https://prove2.me/submissions/9e891f2a-28fa-49ca-bcda-e78997a650b8

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_NormOneCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_IntrinsicStrongApproximation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderNormOneInnerFormReduction_surjective_iff_PSL_le_ambient
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_IndexCartwrightStegerImage_le_ambient
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_PSL_le_IndexCartwrightStegerImage_of_le_ambient


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped PowerSeries.WithPiTopology
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopologicalSpace
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (orderNormOneInnerFormReduction P r level) ↔
      PSL P r level ≤ IndexCartwrightStegerImage P r level := by
  constructor
  · intro hsurj
    exact PSL_le_IndexCartwrightStegerImage_of_le_ambient P r level
      ((orderNormOneInnerFormReduction_surjective_iff_PSL_le_ambient
        P r level).mp hsurj)
  · intro hPSL
    apply (orderNormOneInnerFormReduction_surjective_iff_PSL_le_ambient
      P r level).mpr
    exact hPSL.trans (IndexCartwrightStegerImage_le_ambient P r level)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger

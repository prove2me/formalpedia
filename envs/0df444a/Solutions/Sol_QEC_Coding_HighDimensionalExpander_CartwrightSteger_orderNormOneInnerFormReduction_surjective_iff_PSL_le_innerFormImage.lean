-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOneInnerFormReduction_surjective_iff_PSL_le_innerFormImage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:13:04.490689+00:00
-- url     : https://prove2.me/submissions/e14efcd3-cea2-4094-9c5c-3f5f6800fac0

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_NormOneCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_IntrinsicStrongApproximation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_IndexInnerFormNormOnePGLImage_eq_orderNormOne_range
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_IndexInnerFormNormOnePGLImage_le_innerFormImage
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderNormOneInnerFormReduction_surjective_of_PSL_le_innerFormImage


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped PowerSeries.WithPiTopology
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopologicalSpace
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (orderNormOneInnerFormReduction P r level) ↔
      PSL P r level ≤ IndexInnerFormImage P r level := by
  constructor
  · intro hsurj y hy
    let yPSL : PSL P r level := ⟨y, hy⟩
    obtain ⟨s, hs⟩ := hsurj yPSL
    have hprojective :
        orderNormOneInnerFormReductionToPGL P r level s = y := by
      exact congrArg Subtype.val hs
    have hyNorm : y ∈ IndexInnerFormNormOnePGLImage P r level := by
      rw [IndexInnerFormNormOnePGLImage_eq_orderNormOne_range]
      exact ⟨s, hprojective⟩
    exact IndexInnerFormNormOnePGLImage_le_innerFormImage P r level
      hyNorm
  · exact orderNormOneInnerFormReduction_surjective_of_PSL_le_innerFormImage
      P r level
end QEC.Coding.HighDimensionalExpander.CartwrightSteger

-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.IndexCartwrightStegerImage_le_ambient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:13:07.627699+00:00
-- url     : https://prove2.me/submissions/15336fb3-5947-4d23-9f70-7f247e9411d5

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_NormOneCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_IntrinsicStrongApproximation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped PowerSeries.WithPiTopology
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopologicalSpace
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCartwrightStegerImage P r level ≤
      IndexCartwrightStegerAmbient P r level := by
  rw [IndexCartwrightStegerAmbient,
    IndexCartwrightStegerUnitImage_eq_image]
  exact le_sup_right
end QEC.Coding.HighDimensionalExpander.CartwrightSteger

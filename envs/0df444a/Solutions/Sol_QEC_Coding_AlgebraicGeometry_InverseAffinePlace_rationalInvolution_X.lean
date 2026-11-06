-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:44:47.573571+00:00
-- url     : https://prove2.me/submissions/d78d113c-9eb9-4749-a6e0-36e14913b157

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseChart
import Mathlib.FieldTheory.Separable
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.InverseAffinePlace
open scoped IntermediateField Polynomial RatFunc
variable (k : Type*) [Field k]
namespace QEC.Coding.AlgebraicGeometry.InverseAffinePlace
theorem _root_.solution :
    rationalInvolution k RatFunc.X = (RatFunc.X : RatFunc k)⁻¹ := by
  simp [rationalInvolution]
end QEC.Coding.AlgebraicGeometry.InverseAffinePlace

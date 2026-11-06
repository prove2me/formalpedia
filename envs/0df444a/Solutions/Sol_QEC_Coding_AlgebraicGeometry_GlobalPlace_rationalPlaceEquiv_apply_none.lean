-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:19:54.742544+00:00
-- url     : https://prove2.me/submissions/592403c5-2af8-4744-a14a-bf52ea5a386a

import Mathlib.NumberTheory.RatFunc.Ostrowski
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RatFuncPlaceClassification

set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open MonoidWithZeroHom
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution :
    rationalPlaceEquiv (k := k) none = rationalInfinity k := rfl
end QEC.Coding.AlgebraicGeometry.GlobalPlace

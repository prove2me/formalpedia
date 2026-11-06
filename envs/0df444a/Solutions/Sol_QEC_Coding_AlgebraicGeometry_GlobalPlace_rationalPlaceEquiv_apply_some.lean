-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:20:19.365198+00:00
-- url     : https://prove2.me/submissions/6fd88c91-a5b3-414c-be53-8535d9d40e9b

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
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    rationalPlaceEquiv (k := k) (some p) = rationalAdic p := rfl
end QEC.Coding.AlgebraicGeometry.GlobalPlace

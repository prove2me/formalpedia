-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.RatFuncFixtureDirectIntegralClosure.algebraMap_ringOfIntegersToPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:28:06.776493+00:00
-- url     : https://prove2.me/submissions/dd1241f8-5b94-44d7-a5fd-fb3062437d5a

import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.IsIntegral
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalIntegralClosure

set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.RatFuncFixtureDirectIntegralClosure
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixtureDirectIntegralClosure._p2m_local_instance_c6523eaeb4_13
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixtureDirectIntegralClosure._p2m_local_instance_c6523eaeb4_18
namespace QEC.Coding.AlgebraicGeometry.RatFuncFixtureDirectIntegralClosure
theorem _root_.solution (b : B) :
    algebraMap K[X] F (ringOfIntegersToPolynomial b) = algebraMap B F b :=
  IsIntegralClosure.algebraMap_equiv K[X] B F K[X] b
end QEC.Coding.AlgebraicGeometry.RatFuncFixtureDirectIntegralClosure

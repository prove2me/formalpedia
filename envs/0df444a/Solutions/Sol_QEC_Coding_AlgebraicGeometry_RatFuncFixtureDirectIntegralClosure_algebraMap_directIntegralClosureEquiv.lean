-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.RatFuncFixtureDirectIntegralClosure.algebraMap_directIntegralClosureEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:48:41.81785+00:00
-- url     : https://prove2.me/submissions/03a3241e-a140-4611-8106-674b227e2f8a

import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.IsIntegral
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalIntegralClosure
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncFixtureDirectIntegralClosure_algebraMap_ringOfIntegersToPolynomial

set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.RatFuncFixtureDirectIntegralClosure
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixtureDirectIntegralClosure._p2m_local_instance_c6523eaeb4_13
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixtureDirectIntegralClosure._p2m_local_instance_c6523eaeb4_18
namespace QEC.Coding.AlgebraicGeometry.RatFuncFixtureDirectIntegralClosure
theorem _root_.solution (p : K[X]) :
    algebraMap B F (directIntegralClosureEquiv p) = algebraMap K[X] F p := by
  have h := algebraMap_ringOfIntegersToPolynomial (directIntegralClosureEquiv p)
  simpa only [directIntegralClosureEquiv, AlgEquiv.apply_symm_apply] using h.symm
end QEC.Coding.AlgebraicGeometry.RatFuncFixtureDirectIntegralClosure

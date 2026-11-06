-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.functionFieldDifferentialGenerator_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:45:37.367887+00:00
-- url     : https://prove2.me/submissions/37c5a320-ae4a-4c5d-82d2-40960d6f567c

import Mathlib.RingTheory.Kaehler.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SeparableDerivationExtension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped RatFunc
variable {k F : Type*} [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
theorem _root_.solution :
    functionFieldDifferentialGenerator (k := k) (F := F) ≠ 0 := by
  intro hzero
  have hcoordinate := congrArg
    (functionFieldDifferentialCoordinate (k := k) (F := F)) hzero
  rw [functionFieldDifferentialCoordinate_generator,
    map_zero] at hcoordinate
  exact one_ne_zero hcoordinate
end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential

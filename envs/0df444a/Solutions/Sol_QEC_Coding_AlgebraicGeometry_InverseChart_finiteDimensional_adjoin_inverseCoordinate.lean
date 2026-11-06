-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.InverseChart.finiteDimensional_adjoin_inverseCoordinate
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:29:59.302074+00:00
-- url     : https://prove2.me/submissions/64e45eb2-b3fa-403a-9afd-5a225a165da3

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.NumberTheory.FunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseChart
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.InverseChart
open scoped IntermediateField Polynomial RatFunc
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k k⟮X⟯ F]
variable [_root_.FunctionField k F]
theorem solution :
    FiniteDimensional k⟮(inverseCoordinate k F)⟯ F :=
  _root_.FunctionField.finiteDimensional_of_adjoin_transcendental
    (inverseCoordinate_transcendental k F)

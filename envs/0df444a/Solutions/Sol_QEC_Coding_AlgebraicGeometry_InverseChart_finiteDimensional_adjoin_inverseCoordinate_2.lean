-- Prove2me | solution 2 for QEC.Coding.AlgebraicGeometry.InverseChart.finiteDimensional_adjoin_inverseCoordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:27:10.220336+00:00
-- url     : https://prove2.me/submissions/886dd5e5-6ede-4c90-997f-8ba74256d578

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
namespace QEC.Coding.AlgebraicGeometry.InverseChart
theorem _root_.solution :
    FiniteDimensional k⟮(inverseCoordinate k F)⟯ F :=
  _root_.FunctionField.finiteDimensional_of_adjoin_transcendental
    (inverseCoordinate_transcendental k F)
end QEC.Coding.AlgebraicGeometry.InverseChart

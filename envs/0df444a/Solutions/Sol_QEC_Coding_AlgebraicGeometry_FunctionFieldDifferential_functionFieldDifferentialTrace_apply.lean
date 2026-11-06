-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.functionFieldDifferentialTrace_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:45:44.482935+00:00
-- url     : https://prove2.me/submissions/b384ec85-9671-4361-b731-116a822194ec

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DerivationTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialTrace

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped RatFunc
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
theorem _root_.solution (omega : Differential k F) :
    functionFieldDifferentialTrace (k := k) (F := F) omega =
      Algebra.trace (RatFunc k) F
          (functionFieldDifferentialCoordinate (k := k) (F := F) omega) •
        functionFieldDifferentialGenerator (k := k) (F := RatFunc k) :=
  rfl
end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential

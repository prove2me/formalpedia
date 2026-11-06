-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.rationalDerivation_one_algebraMap_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:15:31.434702+00:00
-- url     : https://prove2.me/submissions/625dec0c-a2a5-4e82-a0ef-c014396a5531

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_MatrixDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialMatrixDerivation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
variable {k : Type*} [Field k]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (p : k[X]) :
    RatFuncDerivation.rationalDerivation (k := k) (M := RatFunc k) 1
        (algebraMap k[X] (RatFunc k) p) =
      algebraMap k[X] (RatFunc k) p.derivative := by
  let D := RatFuncDerivation.rationalDerivation
    (k := k) (M := RatFunc k) 1
  have hX : D RatFunc.X = 1 := by
    exact RatFuncDerivation.rationalDerivation_apply_X (k := k) (1 : RatFunc k)
  calc
    D (algebraMap k[X] (RatFunc k) p) =
        D (Polynomial.aeval RatFunc.X p) := by
          rw [RatFunc.aeval_X_left_eq_algebraMap]
    _ = Polynomial.aeval RatFunc.X p.derivative • D RatFunc.X := by
      rw [Derivation.map_aeval]
    _ = Polynomial.aeval RatFunc.X p.derivative := by
      rw [hX, smul_eq_mul, mul_one]
    _ = algebraMap k[X] (RatFunc k) p.derivative :=
      RatFunc.aeval_X_left_eq_algebraMap p.derivative
end QEC.Coding.AlgebraicGeometry

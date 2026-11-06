-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:14:13.432554+00:00
-- url     : https://prove2.me/submissions/bd04263f-604d-4d0a-8eb7-aa4bbdc31a93

import Mathlib.RingTheory.Derivation.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDerivation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.RatFuncDerivation
open scoped RatFunc
variable {k M : Type*} [Field k] [AddCommGroup M] [Module k M] [Module (RatFunc k) M]
variable [IsScalarTower k (RatFunc k) M]
namespace QEC.Coding.AlgebraicGeometry.RatFuncDerivation
theorem _root_.solution (D : Derivation k (RatFunc k) M) :
    rationalDerivationEquiv (k := k) (M := M) D = D RatFunc.X :=
  rfl
end QEC.Coding.AlgebraicGeometry.RatFuncDerivation

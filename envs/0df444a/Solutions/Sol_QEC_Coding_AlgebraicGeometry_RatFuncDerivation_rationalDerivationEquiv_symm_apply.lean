-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:14:24.630762+00:00
-- url     : https://prove2.me/submissions/019dca4b-6bbe-4666-8575-200ea5d92eb6

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
theorem _root_.solution (m : M) :
    (rationalDerivationEquiv (k := k) (M := M)).symm m = rationalDerivation (k := k) m :=
  rfl
end QEC.Coding.AlgebraicGeometry.RatFuncDerivation

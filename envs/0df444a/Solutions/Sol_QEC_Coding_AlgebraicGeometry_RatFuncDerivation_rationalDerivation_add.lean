-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivation_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:27:46.83536+00:00
-- url     : https://prove2.me/submissions/9a85167d-7281-4714-825f-ab293368e300

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
theorem _root_.solution (m n : M) :
    rationalDerivation (k := k) (m + n) = rationalDerivation (k := k) m
      + rationalDerivation (k := k) n :=
  (rationalDerivationEquiv (k := k) (M := M)).symm.map_add m n
end QEC.Coding.AlgebraicGeometry.RatFuncDerivation

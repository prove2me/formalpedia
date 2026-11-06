-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivation_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:27:46.004099+00:00
-- url     : https://prove2.me/submissions/930a0a05-6f50-42f2-8450-0d823da831e0

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
theorem _root_.solution (a : RatFunc k) (m : M) :
    rationalDerivation (k := k) (a • m) = a • rationalDerivation (k := k) m :=
  (rationalDerivationEquiv (k := k) (M := M)).symm.map_smul a m
end QEC.Coding.AlgebraicGeometry.RatFuncDerivation

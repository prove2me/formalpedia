-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.SeparableDerivationExtension.separableDerivationExtension_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:27:53.390773+00:00
-- url     : https://prove2.me/submissions/845d4771-2a41-446f-a98f-749893ae69af

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDerivation
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Polynomial.Module.AEval
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SeparableDerivationExtension
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_SeparableDerivationExtension_polynomialExtensionDerivation_X

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.SeparableDerivationExtension
open scoped RatFunc
variable {k F M : Type*} [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]
variable [AddCommGroup M] [Module k M] [Module (RatFunc k) M] [Module F M]
variable [IsScalarTower k F M] [IsScalarTower (RatFunc k) F M] [IsScalarTower k (RatFunc k) M]
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableDerivationExtension.moduleKAEval
local notation3 "η" => separableGenerator (k := k) (F := F)
local notation3 "μ" => separableGeneratorMinpoly (k := k) (F := F)
local notation3 "ν" => separableGeneratorValue (k := k) (F := F)
namespace QEC.Coding.AlgebraicGeometry.SeparableDerivationExtension
theorem _root_.solution (D : Derivation k (RatFunc k) M) :
    separableDerivationExtension D η = ν D := by
  rw [show η = Polynomial.aeval η (Polynomial.X : Polynomial (RatFunc k)) by
    rw [Polynomial.aeval_X]]
  rw [separableDerivationExtension, descendPolynomialDerivation_apply_aeval]
  rw [polynomialExtensionDerivation_X]
  rfl
end QEC.Coding.AlgebraicGeometry.SeparableDerivationExtension

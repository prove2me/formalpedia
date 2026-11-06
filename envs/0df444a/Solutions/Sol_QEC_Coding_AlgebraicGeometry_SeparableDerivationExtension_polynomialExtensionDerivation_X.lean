-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.SeparableDerivationExtension.polynomialExtensionDerivation_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:15:30.545453+00:00
-- url     : https://prove2.me/submissions/215be304-97da-448e-83cd-3320ca2c04ca

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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_SeparableDerivationExtension_polynomialExtensionValue_X

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
namespace QEC.Coding.AlgebraicGeometry.SeparableDerivationExtension
theorem _root_.solution (D : Derivation k (RatFunc k) M) (y : F) (v : M) :
    polynomialExtensionDerivation D y v Polynomial.X = Module.AEval.of (RatFunc k) M y v := by
  change Module.AEval.of (RatFunc k) M y
    (polynomialExtensionValue D y v Polynomial.X) = Module.AEval.of (RatFunc k) M y v
  rw [polynomialExtensionValue_X]
end QEC.Coding.AlgebraicGeometry.SeparableDerivationExtension

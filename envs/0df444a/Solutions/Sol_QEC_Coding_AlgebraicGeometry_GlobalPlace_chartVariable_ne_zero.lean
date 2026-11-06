-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.chartVariable_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:58:02.710345+00:00
-- url     : https://prove2.me/submissions/0730bd56-f466-4d23-b3be-5037b51c7c8b

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_EffectiveDimensionBound
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarFamily

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Polynomial Submodule
open scoped BigOperators Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochPolarFamilyAlgebra
attribute [local instance] riemannRochPolarFamilyAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochPolarFamilyPolynomialScalarTower
attribute [local instance] riemannRochPolarFamilyPolynomialScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochPolarFamilyRationalScalarTower
attribute [local instance] riemannRochPolarFamilyRationalScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochPolarFamilyFiniteDimensional
attribute [local instance] riemannRochPolarFamilyFiniteDimensional
omit [Finite k] π τ φ s
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution : chartVariable (k := k) (F := F) ≠ 0 :=
  (map_ne_zero_iff (algebraMap (RatFunc k) F)
    (algebraMap (RatFunc k) F).injective).mpr RatFunc.X_ne_zero
end QEC.Coding.AlgebraicGeometry.GlobalPlace

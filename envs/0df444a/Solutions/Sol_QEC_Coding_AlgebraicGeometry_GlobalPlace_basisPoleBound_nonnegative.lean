-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.basisPoleBound_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:02:22.888046+00:00
-- url     : https://prove2.me/submissions/a9c4f979-ca21-461a-94eb-740fb7233fc7

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_EffectiveDimensionBound
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarFamily
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_nonnegative

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
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution {ι : Type*} [Fintype ι] (b : ι → F) :
    Divisor.Nonnegative (basisPoleBound (k := k) (F := F) b) := by
  intro P
  unfold basisPoleBound
  rw [Finsupp.finsetSum_apply]
  exact Finset.sum_nonneg fun i _ =>
    polarDivisor_nonnegative
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F (b i) P
end QEC.Coding.AlgebraicGeometry.GlobalPlace

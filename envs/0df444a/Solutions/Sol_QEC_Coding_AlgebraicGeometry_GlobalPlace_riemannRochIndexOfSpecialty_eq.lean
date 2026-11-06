-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochIndexOfSpecialty_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:12:37.167429+00:00
-- url     : https://prove2.me/submissions/59e2292e-6401-43a9-a33e-1f719cf643dd

import Mathlib.Data.Int.LeastGreatest
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PrincipalShift
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Genus
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochDimension_lower_bound

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Polynomial Submodule
open scoped Polynomial RatFunc
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochGenusAlgebra
attribute [local instance] riemannRochGenusAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochGenusScalarTower
attribute [local instance] riemannRochGenusScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochGenusFiniteDimensional
attribute [local instance] riemannRochGenusFiniteDimensional
variable [IsFullConstantField k F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    (D : Divisor (GlobalPlace k F)) :
    (riemannRochIndexOfSpecialty
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D : ℤ) =
      (riemannRochDimension D : ℤ) -
        (Divisor.degree (residueDegree (k := k) (F := F)) D + 1 -
          (functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
            (φ := φ) (s := s) k F : ℤ)) := by
  rw [riemannRochIndexOfSpecialty, Int.toNat_of_nonneg]
  exact sub_nonneg.mpr
    (riemannRochDimension_lower_bound
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D)
end QEC.Coding.AlgebraicGeometry.GlobalPlace

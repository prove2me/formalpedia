-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRoch_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:55:31.43319+00:00
-- url     : https://prove2.me/submissions/8a6a18ea-dc6d-4acf-836c-67b14a919542

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialDuality
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Theorem
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochDimension_lower_bound


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochTheoremAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochTheoremScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochTheoremFiniteDimensional
variable [IsFullConstantField k F]
open QEC.Coding.AlgebraicGeometry.GlobalPlace
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution (G : Divisor (GlobalPlace k F)) :
    Divisor.degree (residueDegree (k := k) (F := F)) G + 1 -
        (functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
          (φ := φ) (s := s) k F : ℤ) ≤
      (riemannRochDimension G : ℤ) :=
  riemannRochDimension_lower_bound
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F G
end QEC.Coding.AlgebraicGeometry.GlobalPlace

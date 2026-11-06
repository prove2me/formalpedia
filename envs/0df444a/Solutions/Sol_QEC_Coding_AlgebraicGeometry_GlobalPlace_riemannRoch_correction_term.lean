-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRoch_correction_term
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:59:42.70949+00:00
-- url     : https://prove2.me/submissions/12d2ce3f-c3ac-4f0e-8a3a-07ad38ca9c09

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialDuality
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Theorem
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_differentialDivisor_duality
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochIndexOfSpecialty_eq


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
theorem _root_.solution
    (omega : Differential k F) (homega : omega ≠ 0)
    (G : Divisor (GlobalPlace k F)) :
    (riemannRochDimension G : ℤ) -
        (riemannRochDimension
          (FunctionFieldDifferential.differentialDivisor
            (k := k) (F := F) omega homega - G) : ℤ) =
      Divisor.degree (residueDegree (k := k) (F := F)) G + 1 -
        (functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
          (φ := φ) (s := s) k F : ℤ) := by
  have hduality := differentialDivisor_duality
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F omega homega G
  have hdualityInt := congrArg (fun n : ℕ => (n : ℤ)) hduality
  change
    (riemannRochDimension
      (FunctionFieldDifferential.differentialDivisor
        (k := k) (F := F) omega homega - G) : ℤ) =
      (riemannRochIndexOfSpecialty
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F G : ℤ)
    at hdualityInt
  have hindex := riemannRochIndexOfSpecialty_eq
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F G
  rw [hindex] at hdualityInt
  omega
end QEC.Coding.AlgebraicGeometry.GlobalPlace

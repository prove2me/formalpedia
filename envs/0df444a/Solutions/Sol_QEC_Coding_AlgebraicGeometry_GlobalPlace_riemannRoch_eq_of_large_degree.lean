-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRoch_eq_of_large_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:05:54.858198+00:00
-- url     : https://prove2.me/submissions/188f725b-b2dd-405f-9506-7389576acffb

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialDuality
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Theorem
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRoch_correction_term
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_CanonicalDivisor_degree_eq_two_mul_genus_sub_two
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_sub
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialDivisor_isCanonical
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochDimension_eq_zero_of_negative_degree


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
    (G : Divisor (GlobalPlace k F))
    (hdegree :
      2 * (functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
        (φ := φ) (s := s) k F : ℤ) - 1 ≤
        Divisor.degree (residueDegree (k := k) (F := F)) G) :
    (riemannRochDimension G : ℤ) =
      Divisor.degree (residueDegree (k := k) (F := F)) G + 1 -
        (functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
          (φ := φ) (s := s) k F : ℤ) := by
  let omega := FunctionFieldDifferential.functionFieldDifferentialGenerator
    (k := k) (F := F)
  have homega : omega ≠ 0 :=
    FunctionFieldDifferential.functionFieldDifferentialGenerator_ne_zero
      (k := k) (F := F)
  let K := FunctionFieldDifferential.differentialDivisor
    (k := k) (F := F) omega homega
  have hKcanonical : FunctionFieldDifferential.IsCanonicalDivisor
      (k := k) (F := F) K := by
    exact FunctionFieldDifferential.differentialDivisor_isCanonical
      (k := k) (F := F) omega homega
  have hKdegree := CanonicalDivisor.degree_eq_two_mul_genus_sub_two
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hKcanonical
  have hcomplementDegree :
      Divisor.degree (residueDegree (k := k) (F := F)) (K - G) < 0 := by
    rw [Divisor.degree_sub, hKdegree]
    omega
  have hcomplementZero : riemannRochDimension (K - G) = 0 :=
    riemannRochDimension_eq_zero_of_negative_degree
      (k := k) (F := F) (K - G) hcomplementDegree
  have hcorrection := riemannRoch_correction_term
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
    k F omega homega G
  rw [hcomplementZero] at hcorrection
  omega
end QEC.Coding.AlgebraicGeometry.GlobalPlace

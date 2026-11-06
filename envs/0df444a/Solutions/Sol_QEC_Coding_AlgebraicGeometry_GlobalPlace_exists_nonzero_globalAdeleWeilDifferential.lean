-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.exists_nonzero_globalAdeleWeilDifferential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:36:12.880629+00:00
-- url     : https://prove2.me/submissions/38bcb155-9c75-4238-b29c-b94fe9f32eca

import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleQuotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleWeilDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleDifferentialSpace_finrank_eq_indexOfSpecialty
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_neg
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_finiteDimensional_riemannRochSubmodule
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_chartVariable_degree_eq_finrank
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochDimension_eq_zero_of_negative_degree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochIndexOfSpecialty_eq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


section
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] globalAdeleWeilAlgebra
attribute [local instance] globalAdeleWeilScalarTower
namespace GlobalPlace
attribute [local instance] globalAdeleWeilRiemannRochFiniteDimensional
variable [IsFullConstantField k F]
namespace GlobalAdeleWeilDifferential
variable {k F}
end GlobalAdeleWeilDifferential
attribute [local instance] globalAdeleDifferentialSpaceFinite
private theorem exists_nontrivial_globalAdeleDifferentialSpace :
    ∃ D : Divisor (GlobalPlace k F),
      globalAdeleDifferentialSpace (k := k) (F := F) D ≠ ⊥ := by
  let E : Divisor (GlobalPlace k F) :=
    polarDivisor (k := k) (F := F) (chartVariable (k := k) (F := F))
  let D : Divisor (GlobalPlace k F) := -(E + E)
  have hEdegree : 0 <
      Divisor.degree (residueDegree (k := k) (F := F)) E := by
    rw [show Divisor.degree (residueDegree (k := k) (F := F)) E =
        (Module.finrank (RatFunc k) F : ℤ) by
      exact polarDivisor_chartVariable_degree_eq_finrank
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F]
    exact_mod_cast Module.finrank_pos (R := RatFunc k) (M := F)
  have hDdegree :
      Divisor.degree (residueDegree (k := k) (F := F)) D < 0 := by
    simp only [D, Divisor.degree_neg, Divisor.degree_add]
    omega
  have hDdegreeStrong :
      Divisor.degree (residueDegree (k := k) (F := F)) D ≤ -2 := by
    simp only [D, Divisor.degree_neg, Divisor.degree_add]
    omega
  letI : FiniteDimensional k (riemannRochSubmodule D) :=
    finiteDimensional_riemannRochSubmodule
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D
  have hdimension : riemannRochDimension D = 0 :=
    riemannRochDimension_eq_zero_of_negative_degree
      (k := k) (F := F) D hDdegree
  have hindex := riemannRochIndexOfSpecialty_eq
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D
  have hindexPositive : 0 < riemannRochIndexOfSpecialty
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D := by
    have hgenus : 0 ≤
        (functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
          (φ := φ) (s := s) k F : ℤ) := Int.natCast_nonneg _
    rw [hdimension] at hindex
    have hindexInt : (0 : ℤ) <
        (riemannRochIndexOfSpecialty
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D : ℤ) := by
      omega
    exact_mod_cast hindexInt
  refine ⟨D, fun hbot => ?_⟩
  have hfinrank : 0 < Module.finrank k
      (globalAdeleDifferentialSpace (k := k) (F := F) D) := by
    rw [globalAdeleDifferentialSpace_finrank_eq_indexOfSpecialty
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)]
    exact hindexPositive
  rw [hbot, finrank_bot] at hfinrank
  omega
namespace GlobalAdeleWeilDifferential
variable {k F}
end GlobalAdeleWeilDifferential
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleWeilAlgebra
attribute [local instance] globalAdeleWeilAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleWeilScalarTower
attribute [local instance] globalAdeleWeilScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleWeilRiemannRochFiniteDimensional
attribute [local instance] globalAdeleWeilRiemannRochFiniteDimensional
variable [IsFullConstantField k F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleDifferentialSpaceFinite
attribute [local instance] globalAdeleDifferentialSpaceFinite
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution :
    ∃ omega : GlobalAdeleWeilDifferential k F,
      GlobalAdeleWeilDifferential.IsNonzero omega := by
  obtain ⟨D, hD⟩ := exists_nontrivial_globalAdeleDifferentialSpace
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  obtain ⟨psi, hpsi, hpsiZero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
  exact ⟨⟨psi, ⟨D, hpsi⟩⟩, hpsiZero⟩
end QEC.Coding.AlgebraicGeometry.GlobalPlace

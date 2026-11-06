-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleWeilDifferential_finrank_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:38:59.752611+00:00
-- url     : https://prove2.me/submissions/50d02e33-a8eb-49a1-9e50-e9ff516ee3c5

import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleQuotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleWeilDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleDifferentialSpace_finrank_eq_indexOfSpecialty
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_exists_nonzero_globalAdeleWeilDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_GlobalAdeleWeilDifferential_smulWeil_eq_zero_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleVanishingDivisors_mono
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleSmulIntoDifferentialSpace_coe
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_sub
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_chartVariable_degree_eq_finrank
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochDimension_eq_zero_of_negative_degree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochDimension_lower_bound
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


attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSmulIntoDifferentialSpace_coe
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
namespace GlobalAdeleWeilDifferential
variable {k F}
end GlobalAdeleWeilDifferential
private theorem divisorDegree_nsmul'
    (n : ℕ) (D : Divisor (GlobalPlace k F)) :
    Divisor.degree (residueDegree (k := k) (F := F)) (n • D) =
      (n : ℤ) * Divisor.degree (residueDegree (k := k) (F := F)) D := by
  simpa only [Divisor.degree, nsmul_eq_mul] using
    (Divisor.degreeHom (residueDegree (k := k) (F := F))).map_nsmul n D
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
    Module.finrank F (GlobalAdeleWeilDifferential k F) = 1 := by
  obtain ⟨omega₀, homega₀⟩ :=
    exists_nonzero_globalAdeleWeilDifferential
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  have homega₀ne : omega₀ ≠ 0 := by
    intro hzero
    apply homega₀
    rw [hzero]
    rfl
  refine (finrank_eq_one_iff_of_nonzero' omega₀ homega₀ne).mpr ?_
  intro omega
  by_contra hspan
  push Not at hspan
  have hindependent : ∀ f g : F,
      f • omega₀ + g • omega = 0 → f = 0 ∧ g = 0 := by
    intro f g hfg
    by_cases hg : g = 0
    · subst g
      rw [zero_smul, add_zero] at hfg
      refine ⟨?_, rfl⟩
      by_contra hf
      exact homega₀ne
        ((GlobalAdeleWeilDifferential.smulWeil_eq_zero_iff
          f hf omega₀).mp hfg)
    · exfalso
      apply hspan (g⁻¹ * (-f))
      have hgomega : g • omega = (-f) • omega₀ := by
        have hneg : g • omega = -(f • omega₀) := by
          rw [eq_neg_iff_add_eq_zero, add_comm]
          exact hfg
        rw [hneg, neg_smul]
      have homega : omega = (g⁻¹ * (-f)) • omega₀ := by
        rw [mul_smul, ← hgomega, ← mul_smul, inv_mul_cancel₀ hg, one_smul]
      exact homega.symm
  obtain ⟨D₁, hD₁⟩ := omega₀.vanishes_on
  obtain ⟨D₂, hD₂⟩ := omega.vanishes_on
  let D₀ : Divisor (GlobalPlace k F) := D₁ ⊓ D₂
  have h₀ : D₀ ∈ globalAdeleVanishingDivisors
      (k := k) (F := F) omega₀ :=
    globalAdeleVanishingDivisors_mono
      (k := k) (F := F) inf_le_left hD₁
  have h₂ : D₀ ∈ globalAdeleVanishingDivisors
      (k := k) (F := F) omega :=
    globalAdeleVanishingDivisors_mono
      (k := k) (F := F) inf_le_right hD₂
  let B : Divisor (GlobalPlace k F) :=
    polarDivisor (k := k) (F := F) (chartVariable (k := k) (F := F))
  have hBpositive : 0 <
      Divisor.degree (residueDegree (k := k) (F := F)) B := by
    rw [show Divisor.degree (residueDegree (k := k) (F := F)) B =
        (Module.finrank (RatFunc k) F : ℤ) by
      exact polarDivisor_chartVariable_degree_eq_finrank
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F]
    exact_mod_cast Module.finrank_pos (R := RatFunc k) (M := F)
  have hBone : 1 ≤
      Divisor.degree (residueDegree (k := k) (F := F)) B := hBpositive
  have hcount : ∀ n : ℕ,
      2 * (riemannRochDimension (n • B) : ℤ) ≤
        (riemannRochIndexOfSpecialty
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
          k F (D₀ - n • B) : ℤ) := by
    intro n
    let E : Divisor (GlobalPlace k F) := n • B
    have hinjective : Function.Injective
        (LinearMap.coprod
          (globalAdeleSmulIntoDifferentialSpace
            (k := k) (F := F) omega₀ h₀ E)
          (globalAdeleSmulIntoDifferentialSpace
            (k := k) (F := F) omega h₂ E)) := by
      intro x y hxy
      have hdifference :
          (LinearMap.coprod
            (globalAdeleSmulIntoDifferentialSpace
              (k := k) (F := F) omega₀ h₀ E)
            (globalAdeleSmulIntoDifferentialSpace
              (k := k) (F := F) omega h₂ E)) (x - y) = 0 := by
        rw [map_sub, hxy, sub_self]
      rw [LinearMap.coprod_apply] at hdifference
      have hcoe :
          (GlobalAdeleWeilDifferential.smulWeil
              (((x - y).1 : riemannRochSubmodule E) : F) omega₀).toFun +
            (GlobalAdeleWeilDifferential.smulWeil
              (((x - y).2 : riemannRochSubmodule E) : F) omega).toFun = 0 := by
        have hvalue := congrArg Subtype.val hdifference
        simpa only [Submodule.coe_add,
          globalAdeleSmulIntoDifferentialSpace_coe,
          Submodule.coe_zero] using hvalue
      have hsum :
          ((((x - y).1 : riemannRochSubmodule E) : F) • omega₀ +
            (((x - y).2 : riemannRochSubmodule E) : F) • omega).toFun = 0 := by
        rw [GlobalAdeleWeilDifferential.add_toFun]
        exact hcoe
      have hzero :
          (((x - y).1 : riemannRochSubmodule E) : F) • omega₀ +
            (((x - y).2 : riemannRochSubmodule E) : F) • omega = 0 :=
        GlobalAdeleWeilDifferential.ext hsum
      obtain ⟨hfzero, hgzero⟩ := hindependent _ _ hzero
      have hxyzero : x - y = 0 :=
        Prod.ext (Subtype.ext hfzero) (Subtype.ext hgzero)
      exact sub_eq_zero.mp hxyzero
    have hfinrank :
        Module.finrank k (riemannRochSubmodule E × riemannRochSubmodule E) ≤
          Module.finrank k
            (globalAdeleDifferentialSpace (k := k) (F := F) (D₀ - E)) :=
      LinearMap.finrank_le_finrank_of_injective hinjective
    rw [Module.finrank_prod,
      globalAdeleDifferentialSpace_finrank_eq_indexOfSpecialty] at hfinrank
    have hdimension : Module.finrank k (riemannRochSubmodule E) =
        riemannRochDimension E := rfl
    rw [hdimension] at hfinrank
    dsimp only [E] at hfinrank
    omega
  let genus := functionFieldGenus
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  let M : ℤ := max
    (Divisor.degree (residueDegree (k := k) (F := F)) D₀)
    (3 * (genus : ℤ) - 3 -
      Divisor.degree (residueDegree (k := k) (F := F)) D₀)
  let n : ℕ := M.toNat + 1
  have hnLarge : (n : ℤ) ≥ M + 1 := by
    have hself := Int.self_le_toNat M
    push_cast [n]
    omega
  have hnD₀ : (n : ℤ) >
      Divisor.degree (residueDegree (k := k) (F := F)) D₀ := by
    have hle : Divisor.degree (residueDegree (k := k) (F := F)) D₀ ≤ M :=
      le_max_left _ _
    omega
  have hnGenus : (n : ℤ) > 3 * (genus : ℤ) - 3 -
      Divisor.degree (residueDegree (k := k) (F := F)) D₀ := by
    have hle : 3 * (genus : ℤ) - 3 -
        Divisor.degree (residueDegree (k := k) (F := F)) D₀ ≤ M :=
      le_max_right _ _
    omega
  have hnBDegree : (n : ℤ) *
      Divisor.degree (residueDegree (k := k) (F := F)) B ≥ (n : ℤ) := by
    have hnNonnegative : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    nlinarith [hBone, hnNonnegative]
  have hdegreeSub :
      Divisor.degree (residueDegree (k := k) (F := F)) (D₀ - n • B) =
        Divisor.degree (residueDegree (k := k) (F := F)) D₀ -
          (n : ℤ) *
            Divisor.degree (residueDegree (k := k) (F := F)) B := by
    rw [Divisor.degree_sub, divisorDegree_nsmul']
  have hdegreeNegative :
      Divisor.degree (residueDegree (k := k) (F := F)) (D₀ - n • B) < 0 := by
    rw [hdegreeSub]
    omega
  have hdimensionZero : riemannRochDimension (D₀ - n • B) = 0 :=
    riemannRochDimension_eq_zero_of_negative_degree
      (k := k) (F := F) (D₀ - n • B) hdegreeNegative
  have hindex := riemannRochIndexOfSpecialty_eq
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F (D₀ - n • B)
  rw [hdimensionZero, hdegreeSub] at hindex
  have hlower := riemannRochDimension_lower_bound
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F (n • B)
  rw [divisorDegree_nsmul'] at hlower
  have hcountN := hcount n
  dsimp only [genus] at hnGenus hindex hlower
  omega
end QEC.Coding.AlgebraicGeometry.GlobalPlace

-- Prove2me | solution 1 for P2M_lh_pow_free__ffcdb6e15d31
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:44:15.031152+00:00
-- url     : https://prove2.me/submissions/254ca9ba-8214-4ff4-b5f3-ebe45043fbea

module
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.Henselian
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92
public import Theorems.Thm_lh_pow_free_aux

set_option autoImplicit false
@[expose] public section
public section
open scoped NumberField nonZeroDivisors
open FiniteDimensional NumberField
variable {s r : ℕ} (p : ℕ) {K : Type*} [Field K]
variable {k : Type*} [Field k] (hp : Nat.Prime p)
open Module Finset
open CyclotomicIntegers (zeta)
variable (G : Type*) [AddCommGroup G]
local notation3 "A" => CyclotomicIntegers p
variable
    [Algebra k K] (hKL : finrank k K = p) (σ : K ≃ₐ[k] K)
    (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
local notation "G" =>
  Additive (relativeUnitsWithGenerator p hp hKL σ hσ) ⧸
    AddCommGroup.torsion (Additive (relativeUnitsWithGenerator p hp hKL σ hσ))
local notation "mkG" => unitToU p hp hKL σ hσ
variable [NumberField k]
include hp
theorem _root_.solution {M} [CommGroup M] [Module.Finite ℤ (Additive M)] (ν : M)
    (hk : ∀ (ε : M) (n : ℕ), ε ^ (p ^ n) = 1 → ∃ i, ν ^ i = ε)
    (r) (hr : finrank ℤ (Additive M) + 1 < r) (η : Fin r → Additive M) :
    ∃ (a : ℤ) (ι : Fin r → ℤ) (i : Fin r),
      ∑ i, ι i • η i = (a * p) • Additive.ofMul ν ∧
        ¬ ↑p ∣ ι i ∧ (ν = 1 → ↑i ≠ r - 1) := by
  cases r with
  | zero => exact (not_lt_zero hr).elim
  | succ r =>
    simp only [add_lt_add_iff_right] at hr
    obtain ⟨a₁, ι₁, i₁, e₁, hi₁⟩ := lh_pow_free_aux p hp ν hk r hr
      (η ∘ Fin.castSucc)
    obtain ⟨a₂, ι₂, i₂, e₂, hi₂⟩ := lh_pow_free_aux p hp ν hk r hr
      (η ∘ Fin.succAbove i₁.castSucc)
    by_cases hν' : ν = 1
    · refine ⟨1, Function.extend Fin.castSucc ι₁ 0, Fin.castSucc i₁, ?_,
        by rwa [(Fin.castSucc_injective r).extend_apply], ?_⟩
      · subst hν'
        simp only [Function.comp_apply, ofMul_one, smul_zero] at e₁ ⊢
        rw [← e₁]
        simp [Fin.sum_univ_castSucc, (Fin.castSucc_injective r).extend_apply,
          (Fin.castSucc_lt_last _).ne]
      · rintro -
        simp [(Fin.is_lt _).ne]
    by_cases ha₁ : ↑p ∣ a₁
    · obtain ⟨b, hb⟩ := ha₁
      refine ⟨b, Function.extend Fin.castSucc ι₁ 0, Fin.castSucc i₁, ?_,
        by rwa [(Fin.castSucc_injective r).extend_apply], fun H ↦ (hν' H).elim⟩
      rw [← hb.trans (mul_comm _ _), ← e₁]
      simp [Fin.sum_univ_castSucc, (Fin.castSucc_injective r).extend_apply,
        (Fin.castSucc_lt_last _).ne]
    by_cases ha₂ : ↑p ∣ a₂
    · obtain ⟨b, hb⟩ := ha₂
      refine ⟨b, Function.extend (Fin.succAbove i₁.castSucc) ι₂ 0,
        Fin.succAbove i₁.castSucc i₂, ?_,
        by rwa [Fin.succAbove_right_injective.extend_apply], fun H ↦ (hν' H).elim⟩
      rw [← hb.trans (mul_comm _ _), ← e₂]
      simp [Fin.sum_univ_succAbove _ i₁.castSucc, Fin.succAbove_right_injective.extend_apply]
    obtain ⟨α₁, β₁, h₁⟩ := (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr ha₁
    obtain ⟨α₂, β₂, h₂⟩ := (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr ha₂
    refine ⟨α₂ - α₁,
      β₁ • Function.extend Fin.castSucc ι₁ 0 -
        β₂ • Function.extend (Fin.succAbove i₁.castSucc) ι₂ 0,
      i₁.castSucc, ?_, ?_, fun H ↦ (hν' H).elim⟩
    · rw [sub_mul, eq_sub_iff_add_eq.mpr h₁, eq_sub_iff_add_eq.mpr h₂]
      simp only [zsmul_eq_mul, Pi.intCast_def, Int.cast_id, Pi.sub_apply, Pi.mul_apply,
        sub_sub_sub_cancel_left]
      simp only [sub_smul, mul_smul, ← e₁, ← e₂, sum_sub_distrib]
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_succAbove _ i₁.castSucc]
      simp [(Fin.castSucc_injective r).extend_apply, Fin.succAbove_right_injective.extend_apply,
        (Fin.castSucc_lt_last _).ne, smul_sum]
    · simp only [zsmul_eq_mul, Pi.intCast_def, Int.cast_id, Pi.sub_apply, Pi.mul_apply,
        not_true_eq_false, (Fin.castSucc_injective r).extend_apply,
        Fin.exists_succAbove_eq_iff, ne_eq, not_false_eq_true, Function.extend_apply',
        Pi.zero_apply, mul_zero, sub_zero, (Nat.prime_iff_prime_int.mp hp).dvd_mul, hi₁, not_or,
        and_true]
      intro H
      exact (Nat.prime_iff_prime_int.mp hp).not_dvd_one
        (h₁ ▸ dvd_add (dvd_mul_left (p : ℤ) α₁) (dvd_mul_of_dvd_left H a₁))

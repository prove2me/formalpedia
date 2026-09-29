-- Prove2me | solution 1 for PadicAlgCl.norm_apply_sub_le_norm_apply_sub_of_mem_cyclotomicTower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/eadc9c80-c11b-546e-a99b-57ee4d077bbb

import Mathlib
import Definitions.Def_PadicAlgCl_CyclotomicTower
import Theorems.Thm_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one
import Theorems.Thm_IsCyclotomicExtension_Padic_isIntegralClosure_adjoin_singleton_of_prime_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_norm_apply_sub_le_norm_apply_sub_of_mem_cyclotomicTower

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

namespace TW6

open Polynomial

variable (p : ℕ) [Fact p.Prime]

local notation "Ω" => PadicAlgCl p
local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)

private lemma _root_.TW6.exists_isPrimitiveRoot (n : ℕ) : ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ n) := by
  have hne : p ^ n ≠ 0 := pow_ne_zero n (Fact.out : p.Prime).ne_zero
  haveI : NeZero ((p ^ n : ℕ) : Ω) := ⟨by exact_mod_cast hne⟩
  haveI : IsCyclotomicExtension {p ^ n} Ω Ω := IsSepClosedOfCharZero.isCyclotomicExtension _ _
  exact IsCyclotomicExtension.exists_isPrimitiveRoot Ω Ω (S := {p ^ n}) rfl hne

p2m_export "TW6" "exists_isPrimitiveRoot"
lemma cyclotomicTower_eq_adjoin (n : ℕ) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n)) :
    PadicAlgCl.cyclotomicTower p n = IntermediateField.adjoin ℚ_[p] {ζ} := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  apply le_antisymm
  · unfold PadicAlgCl.cyclotomicTower
    rw [IntermediateField.adjoin_le_iff]
    intro ξ (hξ : ξ ^ (p ^ n) = 1)
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[p] ζ) i
  · exact IntermediateField.adjoin.mono ℚ_[p] _ _ (Set.singleton_subset_iff.mpr hζ.pow_eq_one)

lemma norm_eq_one_of_pow_eq_one {ζ : Ω} {k : ℕ} (h : ζ ^ k = 1) (hk : k ≠ 0) : ‖ζ‖ = 1 := by
  have h1 : ‖ζ‖ ^ k = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk).mp h1

lemma norm_algEquiv (σ : Γ) (x : Ω) : ‖σ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algEquiv_eq]

section Level

variable (n : ℕ)

local notation "K" => (PadicAlgCl.cyclotomicTower p n)

theorem norm_le_one_iff_mem_adjoin {ζ : K} (hζ : IsPrimitiveRoot ζ (p ^ n))
    [IsCyclotomicExtension {p ^ n} ℚ_[p] K] (x : K) :
    ‖(x : Ω)‖ ≤ 1 ↔ x ∈ Algebra.adjoin ℤ_[p] ({ζ} : Set K) := by
  haveI : IsIntegralClosure (Algebra.adjoin ℤ_[p] ({ζ} : Set K)) ℤ_[p] K :=
    IsCyclotomicExtension.Padic.isIntegralClosure_adjoin_singleton_of_prime_pow p n K hζ
  haveI : IsScalarTower ℤ_[p] K Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [← PadicAlgCl.isIntegral_padicInt_iff_norm_le_one p (x : Ω),
    show ((x : K) : Ω) = algebraMap K Ω x from rfl,
    isIntegral_algebraMap_iff (algebraMap K Ω).injective,
    IsIntegralClosure.isIntegral_iff (A := Algebra.adjoin ℤ_[p] ({ζ} : Set K))]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem main {ζ : Ω} (hζΩ : IsPrimitiveRoot ζ (p ^ n)) (σ : Γ) {y : Ω} (hy : y ∈ K)
    (hy1 : ‖y‖ ≤ 1) : ‖σ y - y‖ ≤ ‖σ ζ - ζ‖ := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hζmem : ζ ∈ K := PadicAlgCl.mem_cyclotomicTower_of_pow_eq_one p hζΩ.pow_eq_one
  set ζ' : K := ⟨ζ, hζmem⟩ with hζ'def
  have hinj : Function.Injective (algebraMap K Ω) := (algebraMap K Ω).injective
  have hζ' : IsPrimitiveRoot ζ' (p ^ n) := IsPrimitiveRoot.of_map_of_injective hζΩ hinj
  haveI hcyc : IsCyclotomicExtension {p ^ n} ℚ_[p] K := by
    rw [cyclotomicTower_eq_adjoin p n hζΩ]
    exact hζΩ.intermediateField_adjoin_isCyclotomicExtension ℚ_[p]

  have hy' : (⟨y, hy⟩ : K) ∈ Algebra.adjoin ℤ_[p] ({ζ'} : Set K) :=
    (norm_le_one_iff_mem_adjoin p n hζ' ⟨y, hy⟩).mp hy1

  suffices H : ∀ u : K, u ∈ Algebra.adjoin ℤ_[p] ({ζ'} : Set K) →
      ‖(u : Ω)‖ ≤ 1 ∧ ‖σ u - u‖ ≤ ‖σ ζ - ζ‖ from (H ⟨y, hy⟩ hy').2
  intro u hu
  induction hu using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨(norm_eq_one_of_pow_eq_one p hζΩ.pow_eq_one (NeZero.ne _)).le, le_rfl⟩
  | algebraMap r =>
    refine ⟨?_, ?_⟩
    · change ‖algebraMap ℤ_[p] Ω r‖ ≤ 1
      rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] Ω, norm_algebraMap']
      exact r.2
    · change ‖σ (algebraMap ℤ_[p] Ω r) - algebraMap ℤ_[p] Ω r‖ ≤ _
      rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] Ω, AlgEquiv.commutes, sub_self, norm_zero]
      exact norm_nonneg _
  | add u v _ _ ihu ihv =>
    refine ⟨?_, ?_⟩
    · rw [AddMemClass.coe_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ihu.1 ihv.1)
    · rw [AddMemClass.coe_add, map_add, add_sub_add_comm]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ihu.2 ihv.2)
  | mul u v _ _ ihu ihv =>
    refine ⟨?_, ?_⟩
    · rw [MulMemClass.coe_mul, norm_mul]
      exact mul_le_one₀ ihu.1 (norm_nonneg _) ihv.1
    · have hsplit : σ ((u : Ω) * v) - (u : Ω) * v = σ u * (σ v - v) + (σ u - u) * v := by
        rw [map_mul]; ring
      rw [MulMemClass.coe_mul, hsplit]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul, norm_algEquiv]
        calc ‖(u : Ω)‖ * ‖σ v - v‖ ≤ 1 * ‖σ ζ - ζ‖ :=
              mul_le_mul ihu.1 ihv.2 (norm_nonneg _) zero_le_one
          _ = ‖σ ζ - ζ‖ := one_mul _
      · rw [norm_mul]
        calc ‖σ u - u‖ * ‖(v : Ω)‖ ≤ ‖σ ζ - ζ‖ * 1 :=
              mul_le_mul ihu.2 ihv.1 (norm_nonneg _) (norm_nonneg _)
          _ = ‖σ ζ - ζ‖ := mul_one _

end Level

end TW6

end

theorem solution
    (p : ℕ) [Fact p.Prime] {n : ℕ} {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ n))
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) {y : PadicAlgCl p}
    (hy : y ∈ PadicAlgCl.cyclotomicTower p n) (hy1 : ‖y‖ ≤ 1) :
    ‖σ y - y‖ ≤ ‖σ ζ - ζ‖ :=
  TW6.main p n hζ σ hy hy1

end S_PadicAlgCl_norm_apply_sub_le_norm_apply_sub_of_mem_cyclotomicTower
end P2MW
export P2MW.S_PadicAlgCl_norm_apply_sub_le_norm_apply_sub_of_mem_cyclotomicTower (solution)

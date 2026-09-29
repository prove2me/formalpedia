-- Prove2me | solution 1 for PadicAlgCl.norm_apply_sub_self_eq_of_isPrimitiveRoot_of_mem_fixingSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/b557e938-43e9-53fe-ba06-6ed8c6778d28

import Mathlib
import Definitions.Def_PadicAlgCl_CyclotomicTower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_norm_apply_sub_self_eq_of_isPrimitiveRoot_of_mem_fixingSubgroup

set_option autoImplicit false

noncomputable section

namespace TP9B5

open Polynomial

variable (p : ℕ) [Fact p.Prime]

local notation "Ω" => PadicAlgCl p
local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
local notation "L" => PadicAlgCl.cyclotomicTower p

lemma p_pos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos

lemma norm_natCast_p : ‖(p : Ω)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] Ω) p, norm_algebraMap', Padic.norm_p]

lemma cyclotomicTower_eq_adjoin (n : ℕ) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n)) :
    L n = IntermediateField.adjoin ℚ_[p] {ζ} := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  apply le_antisymm
  · unfold PadicAlgCl.cyclotomicTower
    rw [IntermediateField.adjoin_le_iff]
    intro ξ (hξ : ξ ^ (p ^ n) = 1)
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[p] ζ) i
  · exact IntermediateField.adjoin.mono ℚ_[p] _ _ (Set.singleton_subset_iff.mpr hζ.pow_eq_one)

lemma mem_of_isPrimitiveRoot (n : ℕ) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n)) : ζ ∈ L n :=
  PadicAlgCl.mem_cyclotomicTower_of_pow_eq_one p hζ.pow_eq_one

private lemma _root_.TP9B5.mem_fixingSubgroup_iff (n : ℕ) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n)) (σ : Γ) :
    σ ∈ (L n).fixingSubgroup ↔ σ ζ = ζ := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h
    exact h ζ (mem_of_isPrimitiveRoot p n hζ)
  · intro h x hx
    rw [cyclotomicTower_eq_adjoin p n hζ] at hx
    have hle : IntermediateField.adjoin ℚ_[p] {ζ} ≤
        IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
        IntermediateField.mem_fixedField_iff]
      intro f hf
      obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
      have hnat : ∀ k : ℕ, (σ ^ k) ζ = ζ := by
        intro k
        induction k with
        | zero => simp
        | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, h, ih]
      rcases Int.eq_nat_or_neg z with ⟨k, rfl | rfl⟩
      · rw [zpow_natCast]; exact hnat k
      · rw [zpow_neg, zpow_natCast]
        have h1 := hnat k
        calc (σ ^ k)⁻¹ ζ = (σ ^ k)⁻¹ ((σ ^ k) ζ) := by rw [h1]
          _ = ζ := by rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have hx' := hle hx
    rw [IntermediateField.mem_fixedField_iff] at hx'
    exact hx' σ (Subgroup.mem_zpowers σ)

p2m_export "TP9B5" "mem_fixingSubgroup_iff"
lemma mem_fixingSubgroup_iff_dvd {N n : ℕ} (hn : n ≤ N) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ N))
    (τ : Γ) {b : ℕ} (hb : 1 ≤ b) (hτ : τ ζ = ζ ^ b) :
    τ ∈ (L n).fixingSubgroup ↔ p ^ n ∣ b - 1 := by
  have hpos : 0 < p ^ N := pow_pos (Fact.out : p.Prime).pos N
  have hζn : IsPrimitiveRoot (ζ ^ (p ^ (N - n))) (p ^ n) :=
    hζ.pow hpos (by rw [← pow_add, Nat.sub_add_cancel hn])
  rw [mem_fixingSubgroup_iff p n hζn, map_pow, hτ, ← pow_mul, mul_comm, pow_mul]
  set η : Ω := ζ ^ p ^ (N - n) with hη
  have hη0 : η ≠ 0 := hζn.ne_zero (pow_ne_zero n (Fact.out : p.Prime).ne_zero)
  have hsplit : η ^ b = η ^ (b - 1) * η := by rw [← pow_succ, Nat.sub_add_cancel hb]
  rw [hsplit]
  constructor
  · intro h
    have h1 : η ^ (b - 1) = 1 := by
      have h2 : η ^ (b - 1) * η = 1 * η := by rw [one_mul]; exact h
      exact mul_right_cancel₀ hη0 h2
    exact (hζn.pow_eq_one_iff_dvd _).mp h1
  · intro h
    rw [(hζn.pow_eq_one_iff_dvd _).mpr h, one_mul]

lemma exists_apply_eq_pow {n : ℕ} {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n)) (σ : Γ) :
    ∃ a : ℕ, 1 ≤ a ∧ σ ζ = ζ ^ a := by
  have hpos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  haveI : NeZero (p ^ n) := ⟨hpos.ne'⟩
  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one (ξ := σ ζ)
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  refine ⟨a + p ^ n, le_add_left hpos, ?_⟩
  rw [pow_add, hζ.pow_eq_one, mul_one, ha]

lemma norm_eq_one_of_pow_eq_one {ζ : Ω} {k : ℕ} (h : ζ ^ k = 1) (hk : k ≠ 0) : ‖ζ‖ = 1 := by
  have h1 : ‖ζ‖ ^ k = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk).mp h1

lemma norm_one_sub_pow_le {ζ : Ω} {N : ℕ} (hζ : ζ ^ N = 1) (hN : N ≠ 0) (a : ℕ) :
    ‖1 - ζ ^ a‖ ≤ ‖1 - ζ‖ := by
  have h1 : 1 - ζ ^ a = (∑ i ∈ Finset.range a, ζ ^ i) * (1 - ζ) := by
    have := geom_sum_mul ζ a
    linear_combination this
  rw [h1, norm_mul]
  have h2 : ‖∑ i ∈ Finset.range a, ζ ^ i‖ ≤ 1 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_pow, norm_eq_one_of_pow_eq_one p hζ hN, one_pow]
  calc ‖∑ i ∈ Finset.range a, ζ ^ i‖ * ‖1 - ζ‖ ≤ 1 * ‖1 - ζ‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = ‖1 - ζ‖ := one_mul _

lemma norm_one_sub_eq_of_isPrimitiveRoot {n : ℕ} {ζ μ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n))
    (hμ : IsPrimitiveRoot μ (p ^ n)) : ‖1 - μ‖ = ‖1 - ζ‖ := by
  have hne : p ^ n ≠ 0 := pow_ne_zero n (Fact.out : p.Prime).ne_zero
  haveI : NeZero (p ^ n) := ⟨hne⟩
  obtain ⟨a, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one
  obtain ⟨b, -, hb⟩ := hμ.eq_pow_of_pow_eq_one hζ.pow_eq_one
  apply le_antisymm (norm_one_sub_pow_le p hζ.pow_eq_one hne a)
  have := norm_one_sub_pow_le p hμ.pow_eq_one hne b
  rwa [hb] at this

theorem norm_sub_one_of_isPrimitiveRoot {n : ℕ} (hn : 0 < n) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (p ^ n)) :
    ‖ζ - 1‖ = (p : ℝ) ^ (-(1 : ℝ) / ((p ^ n).totient : ℝ)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩

  have hprod : (p : Ω) = ∏ μ ∈ primitiveRoots (p ^ (k + 1)) Ω, (1 - μ) := by
    have h1 := eval_one_cyclotomic_prime_pow (R := Ω) (p := p) k
    rw [cyclotomic_eq_prod_X_sub_primitiveRoots hζ, eval_prod] at h1
    rw [← h1]
    refine Finset.prod_congr rfl fun μ _ => ?_
    simp
  have hnorm : (p : ℝ)⁻¹ = ‖ζ - 1‖ ^ (p ^ (k + 1)).totient := by
    rw [← norm_natCast_p p, hprod, norm_prod, ← hζ.card_primitiveRoots, ← Finset.prod_const]
    refine Finset.prod_congr rfl fun μ hμ => ?_
    rw [mem_primitiveRoots (pow_pos hp.pos _)] at hμ
    rw [norm_one_sub_eq_of_isPrimitiveRoot p hζ hμ, norm_sub_rev]
  have htot : (p ^ (k + 1)).totient ≠ 0 := (Nat.totient_pos.mpr (pow_pos hp.pos _)).ne'
  have h2 : ‖ζ - 1‖ = ((p : ℝ)⁻¹) ^ (((p ^ (k + 1)).totient : ℝ)⁻¹) := by
    rw [hnorm, Real.pow_rpow_inv_natCast (norm_nonneg _) htot]
  rw [h2, Real.inv_rpow (p_pos p).le, ← Real.rpow_neg (p_pos p).le]
  congr 1
  rw [neg_div, one_div]

lemma isPrimitiveRoot_pow_of_dvd_of_not_dvd {n k : ℕ} (hkn : k < n) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (p ^ n)) {m : ℕ} (hk : p ^ k ∣ m) (hk' : ¬ p ^ (k + 1) ∣ m) :
    IsPrimitiveRoot (ζ ^ m) (p ^ (n - k)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨u, rfl⟩ := hk
  have hu : ¬ p ∣ u := by
    intro h
    apply hk'
    rw [pow_succ]
    exact mul_dvd_mul_left _ h
  have hpos : 0 < p ^ n := pow_pos hp.pos n
  have h1 : IsPrimitiveRoot (ζ ^ (p ^ k)) (p ^ (n - k)) :=
    hζ.pow hpos (by rw [← pow_add, Nat.add_sub_cancel' hkn.le])
  rw [pow_mul]
  refine h1.pow_of_coprime u ?_
  exact (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hu)).symm

theorem main {n k : ℕ} (hkn : k < n) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n)) (σ : Γ)
    (hσ : σ ∈ (L k).fixingSubgroup) (hσ' : σ ∉ (L (k + 1)).fixingSubgroup) :
    ‖σ ζ - ζ‖ = (p : ℝ) ^ (-(1 : ℝ) / ((p ^ (n - k)).totient : ℝ)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨a, ha1, ha⟩ := exists_apply_eq_pow p hζ σ
  have hk : p ^ k ∣ a - 1 := (mem_fixingSubgroup_iff_dvd p hkn.le hζ σ ha1 ha).mp hσ
  have hk' : ¬ p ^ (k + 1) ∣ a - 1 := fun h =>
    hσ' ((mem_fixingSubgroup_iff_dvd p (Nat.succ_le_of_lt hkn) hζ σ ha1 ha).mpr h)
  have hprim : IsPrimitiveRoot (ζ ^ (a - 1)) (p ^ (n - k)) :=
    isPrimitiveRoot_pow_of_dvd_of_not_dvd p hkn hζ hk hk'
  have hfac : σ ζ - ζ = ζ * (ζ ^ (a - 1) - 1) := by
    rw [ha, mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel ha1]
  have hζ1 : ‖ζ‖ = 1 :=
    norm_eq_one_of_pow_eq_one p hζ.pow_eq_one (pow_ne_zero n hp.ne_zero)
  rw [hfac, norm_mul, hζ1, one_mul]
  exact norm_sub_one_of_isPrimitiveRoot p (Nat.sub_pos_of_lt hkn) hprim

end TP9B5

end

theorem solution
    (p : ℕ) [Fact p.Prime] {n k : ℕ} (hkn : k < n) {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ (p ^ n)) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : σ ∈ (PadicAlgCl.cyclotomicTower p k).fixingSubgroup)
    (hσ' : σ ∉ (PadicAlgCl.cyclotomicTower p (k + 1)).fixingSubgroup) :
    ‖ζ - 1‖ = (p : ℝ) ^ (-(1 : ℝ) / ((p ^ n).totient : ℝ)) ∧
      ‖σ ζ - ζ‖ = (p : ℝ) ^ (-(1 : ℝ) / ((p ^ (n - k)).totient : ℝ)) :=
  ⟨TP9B5.norm_sub_one_of_isPrimitiveRoot p (lt_of_le_of_lt (Nat.zero_le k) hkn) hζ,
    TP9B5.main p hkn hζ σ hσ hσ'⟩

end S_PadicAlgCl_norm_apply_sub_self_eq_of_isPrimitiveRoot_of_mem_fixingSubgroup
end P2MW
export P2MW.S_PadicAlgCl_norm_apply_sub_self_eq_of_isPrimitiveRoot_of_mem_fixingSubgroup (solution)

-- Prove2me | solution 1 for PadicAlgCl.finrank_cyclotomicTower_and_pow_mem_fixingSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/9f55efee-663f-5f89-b402-9096356c13e6

import Mathlib
import Definitions.Def_PadicAlgCl_CyclotomicTower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_finrank_cyclotomicTower_and_pow_mem_fixingSubgroup

set_option autoImplicit false

noncomputable section

namespace CYT

open Polynomial

variable (p : ℕ) [Fact p.Prime]

local notation "Ω" => PadicAlgCl p
local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)

private lemma _root_.CYT.exists_isPrimitiveRoot (n : ℕ) : ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ n) := by
  have hne : p ^ n ≠ 0 := pow_ne_zero n (Fact.out : p.Prime).ne_zero
  haveI : NeZero ((p ^ n : ℕ) : Ω) := ⟨by exact_mod_cast hne⟩
  haveI : IsCyclotomicExtension {p ^ n} Ω Ω := IsSepClosedOfCharZero.isCyclotomicExtension _ _
  exact IsCyclotomicExtension.exists_isPrimitiveRoot Ω Ω (S := {p ^ n}) rfl hne

p2m_export "CYT" "exists_isPrimitiveRoot"

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

private lemma _root_.CYT.mem_fixingSubgroup_iff (n : ℕ) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n)) (σ : Γ) :
    σ ∈ (PadicAlgCl.cyclotomicTower p n).fixingSubgroup ↔ σ ζ = ζ := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h
    exact h ζ (PadicAlgCl.mem_cyclotomicTower_of_pow_eq_one p hζ.pow_eq_one)
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

p2m_export "CYT" "mem_fixingSubgroup_iff"

lemma pow_apply_eq_pow_pow (σ : Γ) {ζ : Ω} {a : ℕ} (h : σ ζ = ζ ^ a) (j : ℕ) :
    (σ ^ j) ζ = ζ ^ (a ^ j) := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, h, map_pow, ih, ← pow_mul, ← pow_succ]

lemma mem_fixingSubgroup_iff_dvd {N n : ℕ} (hn : n ≤ N) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ N))
    (τ : Γ) {b : ℕ} (hb : 1 ≤ b) (hτ : τ ζ = ζ ^ b) :
    τ ∈ (PadicAlgCl.cyclotomicTower p n).fixingSubgroup ↔ p ^ n ∣ b - 1 := by
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

lemma pow_p_sub_one_of_dvd {a k : ℕ} (hk : 2 ≤ k) (ha : 1 ≤ a) (h1 : p ^ k ∣ a - 1)
    (h2 : ¬ p ^ (k + 1) ∣ a - 1) : p ^ (k + 1) ∣ a ^ p - 1 ∧ ¬ p ^ (k + 2) ∣ a ^ p - 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨u, hu⟩ := h1
  have hpu : ¬ p ∣ u := by
    rintro ⟨v, rfl⟩
    apply h2
    refine ⟨v, ?_⟩
    rw [hu]; ring
  have ha' : a = p ^ k * u + 1 := by omega

  have hexp : a ^ p = ∑ i ∈ Finset.range (p + 1), (p ^ k * u) ^ i * (p.choose i) := by
    rw [ha', add_pow]
    simp

  have hp1 : p + 1 = (p - 1) + 1 + 1 := by have := hp.one_lt; omega
  have hsplit : ∑ i ∈ Finset.range (p + 1), (p ^ k * u) ^ i * (p.choose i) =
      1 + p ^ k * u * p + ∑ i ∈ Finset.range (p - 1), (p ^ k * u) ^ (i + 2) * (p.choose (i + 2)) := by
    rw [hp1, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [pow_zero, Nat.choose_zero_right, mul_one, zero_add, pow_one,
      Nat.choose_one_right]
    ring

  have htail : p ^ (k + 2) ∣ ∑ i ∈ Finset.range (p - 1), (p ^ k * u) ^ (i + 2) * (p.choose (i + 2)) := by
    apply Finset.dvd_sum
    intro i _
    apply Dvd.dvd.mul_right
    rw [mul_pow, ← pow_mul]
    apply Dvd.dvd.mul_right
    exact pow_dvd_pow p (by nlinarith)
  obtain ⟨M, hM⟩ := htail
  have hkey : a ^ p - 1 = p ^ (k + 1) * u + p ^ (k + 2) * M := by
    rw [hexp, hsplit, hM]
    have : p ^ k * u * p = p ^ (k + 1) * u := by ring
    rw [this]
    omega
  refine ⟨?_, ?_⟩
  · rw [hkey]
    exact dvd_add (dvd_mul_right _ _) (Dvd.dvd.mul_right (pow_dvd_pow p (by omega)) _)
  · rw [hkey]
    intro hdvd
    have h3 : p ^ (k + 2) ∣ p ^ (k + 1) * u :=
      (Nat.dvd_add_left (dvd_mul_right (p ^ (k + 2)) M)).mp hdvd
    rw [pow_succ] at h3
    exact hpu (Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos _) h3)

theorem pow_mem_and_not_mem (m : ℕ) (σ : Γ)
    (hσ : σ ∈ (PadicAlgCl.cyclotomicTower p (m + 2)).fixingSubgroup)
    (hσ' : σ ∉ (PadicAlgCl.cyclotomicTower p (m + 3)).fixingSubgroup) :
    σ ^ p ∈ (PadicAlgCl.cyclotomicTower p (m + 3)).fixingSubgroup ∧
      σ ^ p ∉ (PadicAlgCl.cyclotomicTower p (m + 4)).fixingSubgroup := by
  have hp : p.Prime := Fact.out
  set N := m + 4 with hN
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot p N
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N hp.ne_zero⟩

  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one (ξ := σ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
  have ha' : σ ζ = ζ ^ a := ha.symm

  have ha1 : 1 ≤ a := by
    by_contra h0
    have : a = 0 := by omega
    subst this
    rw [pow_zero] at ha'

    have h1 : ζ = 1 := by
      have := congrArg σ.symm ha'
      simpa using this
    have hone : (p ^ N : ℕ) = 1 := by
      have := hζ.eq_orderOf
      rw [h1, orderOf_one] at this
      exact this
    have : 1 < p ^ N := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  have hσp : (σ ^ p) ζ = ζ ^ (a ^ p) := pow_apply_eq_pow_pow p σ ha' p
  have hap1 : 1 ≤ a ^ p := Nat.one_le_pow _ _ ha1
  rw [mem_fixingSubgroup_iff_dvd p (by omega) hζ σ ha1 ha'] at hσ hσ'
  rw [mem_fixingSubgroup_iff_dvd p (by omega) hζ (σ ^ p) hap1 hσp,
    mem_fixingSubgroup_iff_dvd p (le_refl N) hζ (σ ^ p) hap1 hσp]
  exact pow_p_sub_one_of_dvd p (by omega) ha1 hσ hσ'

lemma isEisensteinAt_padicInt (k : ℕ) :
    (((cyclotomic (p ^ (k + 1)) ℤ).comp (X + 1)).map (Int.castRingHom ℤ_[p])).IsEisensteinAt
      (Ideal.span {(p : ℤ_[p])}) := by
  have hp : p.Prime := Fact.out
  set g : ℤ[X] := (cyclotomic (p ^ (k + 1)) ℤ).comp (X + 1) with hg
  have hZ : g.IsEisensteinAt (Ideal.span {(p : ℤ)}) :=
    cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p k
  have hgm : g.Monic := by
    have : (X + 1 : ℤ[X]) = X + C 1 := by rw [C_1]
    rw [hg, this]
    exact (cyclotomic.monic _ ℤ).comp_X_add_C 1
  have hg'm : (g.map (Int.castRingHom ℤ_[p])).Monic := hgm.map _
  have hdeg : (g.map (Int.castRingHom ℤ_[p])).natDegree = g.natDegree := hgm.natDegree_map _
  have hprime : (Ideal.span {(p : ℤ_[p])}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr PadicInt.prime_p
  refine hg'm.isEisensteinAt_of_mem_of_notMem hprime.ne_top ?_ ?_
  · intro n hn
    rw [hdeg] at hn
    rw [Polynomial.coeff_map, Ideal.mem_span_singleton]
    have h1 := hZ.mem hn
    rw [Ideal.mem_span_singleton] at h1
    exact map_dvd (Int.castRingHom ℤ_[p]) h1
  · intro hmem
    apply hZ.notMem
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem ⊢
    rw [Polynomial.coeff_map, eq_intCast] at hmem
    exact_mod_cast (PadicInt.pow_p_dvd_int_iff 2 (g.coeff 0)).mp hmem

lemma irreducible_cyclotomic (k : ℕ) : Irreducible (cyclotomic (p ^ (k + 1)) ℚ_[p]) := by
  have hp : p.Prime := Fact.out
  have hE := isEisensteinAt_padicInt p k
  have hmap : ((cyclotomic (p ^ (k + 1)) ℤ).comp (X + 1)).map (Int.castRingHom ℤ_[p]) =
      (cyclotomic (p ^ (k + 1)) ℤ_[p]).comp (X + 1) := by
    rw [Polynomial.map_comp, map_cyclotomic, Polynomial.map_add, map_X, Polynomial.map_one]
  rw [hmap] at hE
  have hmon : ((cyclotomic (p ^ (k + 1)) ℤ_[p]).comp (X + 1)).Monic := by
    have : (X + 1 : ℤ_[p][X]) = X + C 1 := by rw [C_1]
    rw [this]
    exact (cyclotomic.monic _ ℤ_[p]).comp_X_add_C 1
  have hprime : (Ideal.span {(p : ℤ_[p])}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr PadicInt.prime_p
  have hdeg : 0 < ((cyclotomic (p ^ (k + 1)) ℤ_[p]).comp (X + 1)).natDegree := by
    rw [natDegree_comp, natDegree_cyclotomic]
    have : (X + 1 : ℤ_[p][X]).natDegree = 1 := by
      have : (X + 1 : ℤ_[p][X]) = X + C 1 := by rw [C_1]
      rw [this, natDegree_X_add_C]
    rw [this, mul_one]
    exact Nat.totient_pos.mpr (pow_pos hp.pos _)
  have hirrZ : Irreducible ((cyclotomic (p ^ (k + 1)) ℤ_[p]).comp (X + 1)) :=
    hE.irreducible hprime hmon.isPrimitive hdeg
  have hirrQ : Irreducible ((cyclotomic (p ^ (k + 1)) ℚ_[p]).comp (X + 1)) := by
    have h := (hmon.irreducible_iff_irreducible_map_fraction_map (K := ℚ_[p])).mp hirrZ
    rwa [Polynomial.map_comp, map_cyclotomic, Polynomial.map_add, map_X, Polynomial.map_one] at h

  have hcomp : (algEquivAevalXAddC (1 : ℚ_[p])) (cyclotomic (p ^ (k + 1)) ℚ_[p]) =
      (cyclotomic (p ^ (k + 1)) ℚ_[p]).comp (X + 1) := by
    simp [algEquivAevalXAddC, comp_eq_aeval]
  rw [← hcomp] at hirrQ
  exact (MulEquiv.irreducible_iff (algEquivAevalXAddC (1 : ℚ_[p])).toMulEquiv).mp hirrQ

theorem finrank_cyclotomicTower (n : ℕ) (hn : 0 < n) :
    Module.finrank ℚ_[p] (PadicAlgCl.cyclotomicTower p n) = (p - 1) * p ^ (n - 1) := by
  have hp : p.Prime := Fact.out
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot p (k + 1)
  haveI : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI := hζ.intermediateField_adjoin_isCyclotomicExtension (K := ℚ_[p])
  rw [cyclotomicTower_eq_adjoin p (k + 1) hζ,
    IsCyclotomicExtension.finrank (IntermediateField.adjoin ℚ_[p] {ζ}) (irreducible_cyclotomic p k),
    Nat.totient_prime_pow hp (Nat.succ_pos k), mul_comm]

end CYT

end

theorem solution (p : ℕ) [Fact p.Prime] :
    (∀ n : ℕ, 0 < n →
      Module.finrank ℚ_[p] (PadicAlgCl.cyclotomicTower p n) = (p - 1) * p ^ (n - 1)) ∧
    (∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
      σ ∈ (PadicAlgCl.cyclotomicTower p (m + 2)).fixingSubgroup →
      σ ∉ (PadicAlgCl.cyclotomicTower p (m + 3)).fixingSubgroup →
        σ ^ p ∈ (PadicAlgCl.cyclotomicTower p (m + 3)).fixingSubgroup ∧
          σ ^ p ∉ (PadicAlgCl.cyclotomicTower p (m + 4)).fixingSubgroup) :=
  ⟨CYT.finrank_cyclotomicTower p, CYT.pow_mem_and_not_mem p⟩

end S_PadicAlgCl_finrank_cyclotomicTower_and_pow_mem_fixingSubgroup
end P2MW
export P2MW.S_PadicAlgCl_finrank_cyclotomicTower_and_pow_mem_fixingSubgroup (solution)

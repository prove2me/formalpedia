-- Prove2me | solution 1 for ValuationSubring.isPGroup_of_forall_mem_iff_smul_sub_mem_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/f4695ac7-c902-58cb-9457-c7acaf0f5355

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_isPGroup_of_forall_mem_iff_smul_sub_mem_sq

set_option autoImplicit false

universe u v

namespace S17C2b

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
variable {A : ValuationSubring L}

theorem smul_sub_mem_of_inertia (τ : ↥(A.decompositionSubgroup K)) (hτ : τ ∈ A.inertiaSubgroup K) (a : ↥A) :
    τ • a - a ∈ IsLocalRing.maximalIdeal ↥A := by
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, IsLocalRing.ResidueField.residue_smul, sub_eq_zero]
  exact DFunLike.congr_fun (MonoidHom.mem_ker.mp hτ) (IsLocalRing.residue (↥A) a)

theorem coe_smul (τ : ↥(A.decompositionSubgroup K)) (a : ↥A) : ((τ • a : ↥A) : L) = (τ : L ≃ₐ[K] L) (a : L) := rfl

variable [IsDiscreteValuationRing ↥A]

theorem exists_smul_sub_eq_mul (τ : ↥(A.decompositionSubgroup K)) (hτ₀ : τ ∈ A.inertiaSubgroup K)
    (hτ : ∀ ϖ : ↥A, Irreducible ϖ → (τ • ϖ - ϖ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A ^ 2) (a : ↥A) :
    ∃ c ∈ IsLocalRing.maximalIdeal ↥A, τ • a - a = c * a := by
  by_cases ha : a = 0
  · exact ⟨0, Ideal.zero_mem _, by rw [ha, smul_zero, sub_zero, mul_zero]⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥A
  obtain ⟨n, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ

  have hspan : IsLocalRing.maximalIdeal ↥A = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have h2 := hτ ϖ hϖ
  rw [pow_two, hspan, Ideal.span_singleton_mul_span_singleton, Ideal.mem_span_singleton'] at h2
  obtain ⟨d, hd⟩ := h2

  have hτϖ : τ • ϖ = (1 + d * ϖ) * ϖ := by
    have : τ • ϖ = ϖ + (τ • ϖ - ϖ) := by ring
    rw [this, ← hd]; ring
  have hm : d * ϖ ∈ IsLocalRing.maximalIdeal ↥A := by
    rw [hspan]; exact Ideal.mul_mem_left _ d (Ideal.mem_span_singleton_self ϖ)
  set m := d * ϖ with hmdef

  have hpow : (1 + m) ^ n - 1 ∈ IsLocalRing.maximalIdeal ↥A := by
    have hdvd : (1 + m) - 1 ∣ (1 + m) ^ n - 1 ^ n := sub_dvd_pow_sub_pow (1 + m) 1 n
    rw [add_sub_cancel_left, one_pow] at hdvd
    exact Ideal.mem_of_dvd _ hdvd hm
  have hw : τ • (w : ↥A) - w ∈ IsLocalRing.maximalIdeal ↥A := smul_sub_mem_of_inertia τ hτ₀ w

  refine ⟨((τ • (w : ↥A) - w) * (1 + m) ^ n + w * ((1 + m) ^ n - 1)) * (w⁻¹ : (↥A)ˣ), ?_, ?_⟩
  · exact Ideal.mul_mem_right _ _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hw) (Ideal.mul_mem_left _ _ hpow))
  · rw [smul_mul', smul_pow', hτϖ, mul_pow]
    have hu : ((w⁻¹ : (↥A)ˣ) : ↥A) * (w : ↥A) = 1 := Units.inv_mul w
    calc τ • (w : ↥A) * ((1 + m) ^ n * ϖ ^ n) - (w : ↥A) * ϖ ^ n
        = ((τ • (w : ↥A) - w) * (1 + m) ^ n + w * ((1 + m) ^ n - 1)) * ϖ ^ n := by ring
      _ = ((τ • (w : ↥A) - w) * (1 + m) ^ n + w * ((1 + m) ^ n - 1)) * (((w⁻¹ : (↥A)ˣ) : ↥A) * w) * ϖ ^ n := by
          rw [hu, mul_one]
      _ = ((τ • (w : ↥A) - w) * (1 + m) ^ n + w * ((1 + m) ^ n - 1)) * ((w⁻¹ : (↥A)ˣ) : ↥A) * ((w : ↥A) * ϖ ^ n) := by
          ring

omit [IsDiscreteValuationRing ↥A] in

theorem isUnit_one_add {c : ↥A} (hc : c ∈ IsLocalRing.maximalIdeal ↥A) : IsUnit (1 + c) := by
  by_contra h
  have h1 : (1 + c : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := (IsLocalRing.mem_maximalIdeal _).mpr h
  have : (1 : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    have := Ideal.sub_mem _ h1 hc
    rwa [add_sub_cancel_right] at this
  exact (IsLocalRing.maximalIdeal.isMaximal ↥A).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)

theorem exists_apply_sub_eq_mul (τ : ↥(A.decompositionSubgroup K)) (hτ₀ : τ ∈ A.inertiaSubgroup K)
    (hτ : ∀ ϖ : ↥A, Irreducible ϖ → (τ • ϖ - ϖ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A ^ 2) (x : L) :
    ∃ m ∈ IsLocalRing.maximalIdeal ↥A, (τ : L ≃ₐ[K] L) x - x = (m : L) * x := by

  obtain ⟨a, b, hb, rfl⟩ : ∃ a b : ↥A, (b : L) ≠ 0 ∧ x = (a : L) / (b : L) := by
    by_cases hx0 : x = 0
    · exact ⟨0, 1, by simp, by simp [hx0]⟩
    rcases A.mem_or_inv_mem x with hx | hx
    · exact ⟨⟨x, hx⟩, 1, by simp, by simp⟩
    · exact ⟨1, ⟨x⁻¹, hx⟩, by simpa using hx0, by simp⟩
  obtain ⟨c₁, hc₁, h₁⟩ := exists_smul_sub_eq_mul τ hτ₀ hτ a
  obtain ⟨c₂, hc₂, h₂⟩ := exists_smul_sub_eq_mul τ hτ₀ hτ b
  have hτa : τ • a = (1 + c₁) * a := by rw [add_mul, one_mul, ← h₁]; ring
  have hτb : τ • b = (1 + c₂) * b := by rw [add_mul, one_mul, ← h₂]; ring
  have ha' : (τ : L ≃ₐ[K] L) (a : L) = ((1 + c₁ : ↥A) : L) * a := by
    rw [← coe_smul, hτa, MulMemClass.coe_mul]
  have hb' : (τ : L ≃ₐ[K] L) (b : L) = ((1 + c₂ : ↥A) : L) * b := by
    rw [← coe_smul, hτb, MulMemClass.coe_mul]
  obtain ⟨e, he⟩ := (isUnit_one_add hc₂).exists_right_inv
  have hmul : (1 + (c₂ : L)) * (e : L) = 1 := by
    have := congrArg (fun z : ↥A => (z : L)) he
    push_cast at this
    exact this
  have hne : (1 + (c₂ : L)) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    exact zero_ne_one hmul
  have he' : ((e : ↥A) : L) = (1 + (c₂ : L))⁻¹ := eq_inv_of_mul_eq_one_right hmul
  refine ⟨(c₁ - c₂) * e, Ideal.mul_mem_right _ _ (Ideal.sub_mem _ hc₁ hc₂), ?_⟩
  rw [map_div₀, ha', hb']
  push_cast
  rw [he']
  field_simp
  ring

end S17C2b

open S17C2b in
theorem solution
    (K : Type u) [Field K] {L : Type v} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing ↥A]
    (p : ℕ) [Fact p.Prime] (hp : (p : ↥A) ∈ IsLocalRing.maximalIdeal ↥A)
    (Pw : Subgroup ↥(A.inertiaSubgroup K))
    (hPw : ∀ σ : ↥(A.inertiaSubgroup K), σ ∈ Pw ↔
        ∀ ϖ : ↥A, Irreducible ϖ →
          ((σ : ↥(A.decompositionSubgroup K)) • ϖ - ϖ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A ^ 2) :
    IsPGroup p ↥Pw := by
  classical
  letI : Fintype ↥Pw := Fintype.ofFinite ↥Pw

  suffices key : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Fintype.card ↥Pw → ℓ = p by
    rw [IsPGroup.iff_card, ← Fintype.card_eq_nat_card]
    exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Fintype.card_ne_zero (fun hd hdvd => key _ hd hdvd)⟩
  intro ℓ hℓ hℓdvd
  by_contra hℓp
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card ℓ hℓdvd

  let ι : ↥Pw → (L ≃ₐ[K] L) := fun h => (((h : ↥(A.inertiaSubgroup K)) : ↥(A.decompositionSubgroup K)) : L ≃ₐ[K] L)
  have hι_pow : ∀ (h : ↥Pw) (i : ℕ), ι (h ^ i) = ι h ^ i := fun h i => rfl
  have hι_one : ι 1 = 1 := rfl
  have hι_inj : Function.Injective ι := fun h h' hh => Subtype.ext (Subtype.ext (Subtype.ext hh))
  set σ := ι g with hσ
  have hσℓ : σ ^ ℓ = 1 := by rw [hσ, ← hι_pow, ← hg, pow_orderOf_eq_one, hι_one]

  have hmove : ∀ (i : ℕ) (x : L), ∃ m ∈ IsLocalRing.maximalIdeal ↥A, (σ ^ i) x - x = (m : L) * x := by
    intro i x
    have hmem : ((g ^ i : ↥Pw) : ↥(A.inertiaSubgroup K)) ∈ Pw := (g ^ i).2
    obtain ⟨m, hm, h⟩ := exists_apply_sub_eq_mul (K := K)
      (((g ^ i : ↥Pw) : ↥(A.inertiaSubgroup K)) : ↥(A.decompositionSubgroup K))
      ((g ^ i : ↥Pw) : ↥(A.inertiaSubgroup K)).2 ((hPw _).mp hmem) x
    refine ⟨m, hm, ?_⟩
    rw [hσ, ← hι_pow]
    exact h

  have hℓunit : IsUnit ((ℓ : ℕ) : ↥A) := by
    by_contra h
    have hℓmem : ((ℓ : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := (IsLocalRing.mem_maximalIdeal _).mpr h
    have hcop : IsCoprime ((p : ℤ) : ↥A) ((ℓ : ℤ) : ↥A) := by
      have h1 : IsCoprime (p : ℤ) (ℓ : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes Fact.out hℓ).mpr (Ne.symm hℓp))
      exact h1.map (Int.castRingHom ↥A)
    obtain ⟨u, v, huv⟩ := hcop
    push_cast at huv
    have : (1 : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
      rw [← huv]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hp) (Ideal.mul_mem_left _ _ hℓmem)
    exact (IsLocalRing.maximalIdeal.isMaximal ↥A).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)

  let T : L →ₗ[K] L := ∑ i ∈ Finset.range ℓ, (σ ^ i).toLinearMap
  have hT : ∀ x : L, T x = ∑ i ∈ Finset.range ℓ, (σ ^ i) x := by
    intro x
    simp [T]
  have hTunit : ∀ x : L, ∃ u : ↥A, IsUnit u ∧ T x = (u : L) * x := by
    intro x
    choose m hm hmx using fun i => hmove i x
    have hsum : ∑ i ∈ Finset.range ℓ, m i ∈ IsLocalRing.maximalIdeal ↥A := Ideal.sum_mem _ fun i _ => hm i
    refine ⟨(ℓ : ↥A) + ∑ i ∈ Finset.range ℓ, m i, ?_, ?_⟩
    · by_contra hnu
      have hmem : (ℓ : ↥A) + ∑ i ∈ Finset.range ℓ, m i ∈ IsLocalRing.maximalIdeal ↥A :=
        (IsLocalRing.mem_maximalIdeal _).mpr hnu
      have : ((ℓ : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
        have := Ideal.sub_mem _ hmem hsum
        rwa [add_sub_cancel_right] at this
      exact (IsLocalRing.mem_maximalIdeal _).mp this hℓunit
    · rw [hT]
      have : ∀ i ∈ Finset.range ℓ, (σ ^ i) x = x + (m i : L) * x := fun i _ => by rw [← hmx i]; ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ← Finset.sum_mul]
      push_cast
      ring

  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨u, hu, hux⟩ := hTunit x
    rw [hux] at hx
    rcases mul_eq_zero.mp hx with h | h
    · exfalso
      apply hu.ne_zero
      exact_mod_cast h
    · exact h
  have hTsurj : Function.Surjective T := LinearMap.injective_iff_surjective.mp hTinj

  have hσT : ∀ x : L, σ (T x) = T x := by
    intro x
    rw [hT, map_sum]
    have h1 : ∑ i ∈ Finset.range ℓ, σ ((σ ^ i) x) = ∑ i ∈ Finset.range ℓ, (σ ^ (i + 1)) x := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ']
      rfl
    rw [h1]
    have h2 : ∑ i ∈ Finset.range (ℓ + 1), (σ ^ i) x = ∑ i ∈ Finset.range ℓ, (σ ^ i) x + (σ ^ ℓ) x :=
      Finset.sum_range_succ _ _
    have h3 : ∑ i ∈ Finset.range (ℓ + 1), (σ ^ i) x = ∑ i ∈ Finset.range ℓ, (σ ^ (i + 1)) x + (σ ^ 0) x :=
      Finset.sum_range_succ' _ _
    have key := h3.symm.trans h2
    rw [pow_zero, hσℓ] at key
    exact add_right_cancel key

  have hσ1 : σ = 1 := by
    apply AlgEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := hTsurj y
    exact hσT x
  have hg1 : g = 1 := hι_inj (by rw [← hσ, hσ1, hι_one])
  rw [hg1, orderOf_one] at hg
  exact hℓ.one_lt.ne hg

end S_ValuationSubring_isPGroup_of_forall_mem_iff_smul_sub_mem_sq
end P2MW
export P2MW.S_ValuationSubring_isPGroup_of_forall_mem_iff_smul_sub_mem_sq (solution)

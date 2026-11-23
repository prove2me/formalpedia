-- Prove2me | solution 1 for SumProduct.idealCount_prime_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:01:22.081107+00:00
-- url     : https://prove2.me/submissions/8e238a8b-9175-4275-a223-c41f53853820

import Mathlib
import Definitions.Def_SumProduct_EulerBound
section
open scoped NumberField
open NumberField UniqueFactorizationMonoid
namespace SumProduct
variable {K : Type*} [Field K] [NumberField K]
private lemma prod_normalizedFactors_ideal {K : Type*} [Field K] [NumberField K]
    {I : Ideal (𝓞 K)} (hI : I ≠ 0) : (normalizedFactors I).prod = I :=
  associated_iff_eq.mp (prod_normalizedFactors hI)
private lemma factor_mem_primesOverFinset {K : Type*} [Field K] [NumberField K] {p : ℕ}
    (hp : p.Prime) {k : ℕ} {I 𝔭 : Ideal (𝓞 K)} (hI : Ideal.absNorm I = p ^ k)
    (h𝔭 : 𝔭 ∈ normalizedFactors I) :
    𝔭 ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K) := by
  have hprime : Prime 𝔭 := prime_of_normalized_factor 𝔭 h𝔭
  have hmax : 𝔭.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
  have hdvd : 𝔭 ∣ I := dvd_of_mem_normalizedFactors h𝔭
  have hle : I ≤ 𝔭 := Ideal.dvd_iff_le.mp hdvd
  have hnorm_dvd : Ideal.absNorm 𝔭 ∣ Ideal.absNorm I := Ideal.absNorm_dvd_absNorm_of_le hle
  obtain ⟨q, j, hj, _, hq, hQq⟩ := Ideal.exists_prime_and_absNorm_eq_pow 𝔭
  -- `q^j = |𝔭| ∣ p^k`, so the prime `q` equals `p`.
  have hqdvd : q ∣ p ^ k := by
    rw [hQq, hI] at hnorm_dvd; exact dvd_trans (dvd_pow_self q hj.ne') hnorm_dvd
  have hpq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqdvd)
  have hpdvd : (p : ℕ) ∣ Ideal.absNorm 𝔭 := by
    rw [hQq, hpq]; exact dvd_pow_self p hj.ne'
  obtain ⟨P, hPmax, hPunder, hPdvd⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp 𝔭 hpdvd
  -- `P ∣ 𝔭` with both maximal forces `P = 𝔭`, so `𝔭` lies over `p`.
  have hP𝔭 : P = 𝔭 := (hmax.eq_of_le hPmax.ne_top (Ideal.dvd_iff_le.mp hPdvd)).symm
  rw [hP𝔭] at hPunder
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI hpMax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ).isMaximal (by simpa using hpZ.ne_zero)
  have hLO : 𝔭.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hPunder.symm⟩
  exact (IsDedekindDomain.mem_primesOverFinset_iff (by simpa using hpZ.ne_zero) (𝓞 K)).mpr
    ⟨Ideal.isPrime_of_prime hprime, hLO⟩
end SumProduct
end

set_option autoImplicit true
open scoped NumberField
open NumberField UniqueFactorizationMonoid
open SumProduct
variable {K : Type*} [Field K] [NumberField K]
set_option maxHeartbeats 800000
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime)
    (k : ℕ) :
    idealCount K (p ^ k) ≤ Nat.multichoose (Module.finrank ℚ K) k := by
  classical
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI hpMax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ).isMaximal (by simpa using hpZ.ne_zero)
  have hpb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hpZ.ne_zero
  set G := IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K) with hG
  have hGcard : G.card ≤ Module.finrank ℚ K :=
    Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hpb
  -- For `𝔭 ∈ G`: it lies over `p`, has positive inertia degree, and norm `p^{f_𝔭}`.
  have hLO : ∀ 𝔭 ∈ G, 𝔭.LiesOver (Ideal.span {(p : ℤ)}) ∧ 𝔭.IsPrime :=
    fun 𝔭 h𝔭 => ⟨((IsDedekindDomain.mem_primesOverFinset_iff hpb (𝓞 K)).mp h𝔭).2,
      ((IsDedekindDomain.mem_primesOverFinset_iff hpb (𝓞 K)).mp h𝔭).1⟩
  have hfpos : ∀ 𝔭 ∈ G, 0 < (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔭 := by
    intro 𝔭 h𝔭
    obtain ⟨hlo, hpr⟩ := hLO 𝔭 h𝔭
    exact Nat.pos_of_ne_zero (Ideal.inertiaDeg_ne_zero _ _)
  have hnorm𝔭 : ∀ 𝔭 ∈ G, Ideal.absNorm 𝔭 = p ^ ((Ideal.span {(p : ℤ)}).inertiaDeg' 𝔭) := by
    intro 𝔭 h𝔭
    obtain ⟨hlo, hpr⟩ := hLO 𝔭 h𝔭
    have := Ideal.absNorm_eq_pow_inertiaDeg 𝔭 hpZ
    simpa using this
  -- The injection `I ↦ (𝔭 ↦ v_𝔭(I)·f_𝔭)` supported on `G`.
  set Φ : {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} → (Ideal (𝓞 K) →₀ ℕ) :=
    fun I => Finsupp.indicator G
      (fun 𝔭 _ => (normalizedFactors I.1).count 𝔭 * (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔭) with hΦ
  -- All prime factors of `I` (norm `p^k`) lie in `G`, hence `count = 0` off `G`.
  have hcount_off : ∀ (I : Ideal (𝓞 K)), Ideal.absNorm I = p ^ k →
      ∀ 𝔭 ∉ G, (normalizedFactors I).count 𝔭 = 0 := by
    intro I hI 𝔭 h𝔭
    by_contra h
    exact h𝔭 (factor_mem_primesOverFinset hp hI (Multiset.count_pos.mp (Nat.pos_of_ne_zero h)))
  -- The key norm identity: `∑_{𝔭∈G} v_𝔭(I)·f_𝔭 = k`.
  have hsum : ∀ (I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k}),
      ∑ 𝔭 ∈ G, (normalizedFactors I.1).count 𝔭 * (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔭 = k := by
    rintro ⟨I, hI⟩
    have hI0 : I ≠ 0 := by
      rintro rfl
      rw [Ideal.zero_eq_bot, Ideal.absNorm_bot] at hI
      exact (pow_ne_zero k hp.pos.ne') hI.symm
    have habs : (Multiset.map Ideal.absNorm (normalizedFactors I)).prod = Ideal.absNorm I := by
      rw [← map_multiset_prod, prod_normalizedFactors_ideal hI0]
    have step1 : ∀ 𝔭 ∈ G, p ^ ((normalizedFactors I).count 𝔭 *
        (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔭) = Ideal.absNorm 𝔭 ^ (normalizedFactors I).count 𝔭 := by
      intro 𝔭 h𝔭
      rw [hnorm𝔭 𝔭 h𝔭, ← pow_mul, mul_comm]
    have hsub : (normalizedFactors I).toFinset ⊆ G :=
      fun 𝔭 h𝔭 => factor_mem_primesOverFinset hp hI (Multiset.mem_toFinset.mp h𝔭)
    have hone : ∀ 𝔭 ∈ G, 𝔭 ∉ (normalizedFactors I).toFinset →
        Ideal.absNorm 𝔭 ^ (normalizedFactors I).count 𝔭 = 1 := by
      intro 𝔭 _ h𝔭
      rw [Multiset.count_eq_zero.mpr (fun hmem => h𝔭 (Multiset.mem_toFinset.mpr hmem)), pow_zero]
    have hpow : p ^ (∑ 𝔭 ∈ G, (normalizedFactors I).count 𝔭 *
        (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔭) = p ^ k :=
      calc p ^ (∑ 𝔭 ∈ G, (normalizedFactors I).count 𝔭 * (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔭)
          = ∏ 𝔭 ∈ G, p ^ ((normalizedFactors I).count 𝔭 * (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔭) :=
            (Finset.prod_pow_eq_pow_sum G _ p).symm
        _ = ∏ 𝔭 ∈ G, Ideal.absNorm 𝔭 ^ (normalizedFactors I).count 𝔭 := Finset.prod_congr rfl step1
        _ = ∏ 𝔭 ∈ (normalizedFactors I).toFinset, Ideal.absNorm 𝔭 ^ (normalizedFactors I).count 𝔭 :=
            (Finset.prod_subset hsub hone).symm
        _ = (Multiset.map Ideal.absNorm (normalizedFactors I)).prod :=
            (Finset.prod_multiset_map_count _ _).symm
        _ = Ideal.absNorm I := habs
        _ = p ^ k := hI
    exact Nat.pow_right_injective hp.two_le hpow
  -- `Φ` lands in the antidiagonal.
  have hval : ∀ (I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k}) 𝔭, 𝔭 ∈ G →
      (Φ I) 𝔭 = (normalizedFactors I.1).count 𝔭 * (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔭 := by
    intro I 𝔭 h𝔭
    simp only [hΦ]
    exact Finsupp.indicator_of_mem h𝔭 _
  have hsupp : ∀ (I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k}), (Φ I).support ⊆ G := by
    intro I
    simp only [hΦ]
    exact Finsupp.support_indicator_subset G _
  have hmem : ∀ I, Φ I ∈ G.finsuppAntidiag k := by
    intro I
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, hsupp I⟩
    change ∑ 𝔭 ∈ G, (Φ I) 𝔭 = k
    rw [Finset.sum_congr rfl (hval I)]
    exact hsum I
  -- `Φ` is injective.
  have hinj : Function.Injective Φ := by
    rintro ⟨I, hI⟩ ⟨J, hJ⟩ hIJ
    have hI0 : I ≠ 0 := by
      rintro rfl; rw [Ideal.zero_eq_bot, Ideal.absNorm_bot] at hI
      exact pow_ne_zero k hp.pos.ne' hI.symm
    have hJ0 : J ≠ 0 := by
      rintro rfl; rw [Ideal.zero_eq_bot, Ideal.absNorm_bot] at hJ
      exact pow_ne_zero k hp.pos.ne' hJ.symm
    have hcounts : normalizedFactors I = normalizedFactors J := by
      ext 𝔭
      by_cases h𝔭 : 𝔭 ∈ G
      · have key : (normalizedFactors I).count 𝔭 * (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔭
            = (normalizedFactors J).count 𝔭 * (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔭 := by
          have h2 := DFunLike.congr_fun hIJ 𝔭
          simpa only [hΦ, Finsupp.indicator_of_mem h𝔭] using h2
        exact Nat.eq_of_mul_eq_mul_right (hfpos 𝔭 h𝔭) key
      · rw [hcount_off I hI 𝔭 h𝔭, hcount_off J hJ 𝔭 h𝔭]
    have : I = J := by
      rw [← prod_normalizedFactors_ideal hI0, ← prod_normalizedFactors_ideal hJ0, hcounts]
    simpa using this
  -- Counting.
  calc idealCount K (p ^ k)
      = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} := rfl
    _ ≤ Nat.card ↥(G.finsuppAntidiag k) :=
        Nat.card_le_card_of_injective (fun I => ⟨Φ I, hmem I⟩)
          (fun a b h => hinj (Subtype.mk_eq_mk.mp h))
    _ = (G.finsuppAntidiag k).card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = Nat.multichoose G.card k := Finset.card_finsuppAntidiag_nat_eq_multichoose k
    _ ≤ Nat.multichoose (Module.finrank ℚ K) k := by
        rw [Nat.multichoose_eq, Nat.multichoose_eq]
        exact Nat.choose_le_choose k (Nat.sub_le_sub_right (Nat.add_le_add_right hGcard k) 1)
end SumProduct

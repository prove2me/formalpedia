-- Prove2me | solution 1 for SumProduct.idealCount_mul_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:59:58.534316+00:00
-- url     : https://prove2.me/submissions/2778ee6e-6ef2-405e-bd01-3b997a451432

import Mathlib
import Definitions.Def_SumProduct_EulerBound
section
open scoped NumberField
open NumberField UniqueFactorizationMonoid
namespace SumProduct
variable {K : Type*} [Field K] [NumberField K]
private lemma isCoprime_of_coprime_absNorm {K : Type*} [Field K] [NumberField K]
    {I J : Ideal (𝓞 K)} (h : Nat.Coprime (Ideal.absNorm I) (Ideal.absNorm J)) : IsCoprime I J := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  obtain ⟨M, hM, hIJM⟩ := Ideal.exists_le_maximal _ hne
  have hdI : Ideal.absNorm M ∣ Ideal.absNorm I :=
    Ideal.absNorm_dvd_absNorm_of_le (le_trans le_sup_left hIJM)
  have hdJ : Ideal.absNorm M ∣ Ideal.absNorm J :=
    Ideal.absNorm_dvd_absNorm_of_le (le_trans le_sup_right hIJM)
  exact hM.ne_top (Ideal.absNorm_eq_one_iff.mp (Nat.dvd_one.mp (h ▸ Nat.dvd_gcd hdI hdJ)))
private lemma prod_normalizedFactors_ideal {K : Type*} [Field K] [NumberField K]
    {I : Ideal (𝓞 K)} (hI : I ≠ 0) : (normalizedFactors I).prod = I :=
  associated_iff_eq.mp (prod_normalizedFactors hI)
private lemma exists_split {K : Type*} [Field K] [NumberField K] {m n : ℕ}
    (hmn : Nat.Coprime m n) (hm : m ≠ 0) (hn : n ≠ 0) {L : Ideal (𝓞 K)}
    (hL : Ideal.absNorm L = m * n) :
    ∃ I J : Ideal (𝓞 K), Ideal.absNorm I = m ∧ Ideal.absNorm J = n ∧ I * J = L := by
  have hL0 : L ≠ 0 := by
    intro h; rw [h, Ideal.zero_eq_bot, Ideal.absNorm_bot] at hL
    exact (mul_ne_zero hm hn) hL.symm
  classical
  set I : Ideal (𝓞 K) :=
    ((normalizedFactors L).filter (fun P => Nat.Coprime (Ideal.absNorm P) n)).prod with hIdef
  set J : Ideal (𝓞 K) :=
    ((normalizedFactors L).filter (fun P => ¬ Nat.Coprime (Ideal.absNorm P) n)).prod with hJdef
  have hsplit : (normalizedFactors L).filter (fun P => Nat.Coprime (Ideal.absNorm P) n)
      + (normalizedFactors L).filter (fun P => ¬ Nat.Coprime (Ideal.absNorm P) n)
      = normalizedFactors L := Multiset.filter_add_not _ _
  have hIJ : I * J = L := by
    rw [hIdef, hJdef, ← Multiset.prod_add, hsplit, prod_normalizedFactors_ideal hL0]
  have hnorm : Ideal.absNorm I * Ideal.absNorm J = m * n := by rw [← map_mul, hIJ, hL]
  -- `I`'s factors have norm coprime to `n`, so `absNorm I` is coprime to `n`.
  have hcopIn : Nat.Coprime (Ideal.absNorm I) n := by
    rw [hIdef, map_multiset_prod]
    refine Multiset.prod_induction (Nat.Coprime · n) _ (fun a b => Nat.Coprime.mul_left)
      (Nat.coprime_one_left n) ?_
    intro x hx
    simp only [Multiset.mem_map] at hx
    obtain ⟨P, hP, rfl⟩ := hx
    exact (Multiset.mem_filter.mp hP).2
  -- `J`'s factors have norm a prime power `q^j` with `q ∣ n`, hence coprime to `m`.
  have hcopMJ : Nat.Coprime m (Ideal.absNorm J) := by
    rw [hJdef, map_multiset_prod]
    refine Multiset.prod_induction (Nat.Coprime m ·) _ (fun a b => Nat.Coprime.mul_right)
      (Nat.coprime_one_right m) ?_
    intro x hx
    simp only [Multiset.mem_map] at hx
    obtain ⟨P, hP, rfl⟩ := hx
    have hPmem : P ∈ normalizedFactors L := Multiset.mem_of_mem_filter hP
    have hPnc : ¬ Nat.Coprime (Ideal.absNorm P) n := by
      have := (Multiset.mem_filter.mp hP).2; simpa using this
    have hPprime : Prime P := prime_of_normalized_factor P hPmem
    have hP0 : P ≠ ⊥ := hPprime.ne_zero
    have hPmax : P.IsMaximal := (Ideal.isPrime_of_prime hPprime).isMaximal hP0
    obtain ⟨q, j, hj, _, hq, hPq⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
    rw [hPq] at hPnc ⊢
    have hqn : q ∣ n := by
      by_contra hqn
      exact hPnc ((Nat.coprime_pow_left_iff hj q n).mpr
        ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqn))
    exact (Nat.Coprime.coprime_dvd_right hqn hmn).pow_right j
  have hIm : Ideal.absNorm I = m :=
    Nat.dvd_antisymm
      (hcopIn.dvd_of_dvd_mul_right ⟨_, hnorm.symm⟩)
      (hcopMJ.dvd_of_dvd_mul_right (by rw [hnorm]; exact dvd_mul_right m n))
  have hJn : Ideal.absNorm J = n := by
    have h2 : m * Ideal.absNorm J = m * n := hIm ▸ hnorm
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm) h2
  exact ⟨I, J, hIm, hJn, hIJ⟩
end SumProduct
end

set_option autoImplicit true
open scoped NumberField
open NumberField UniqueFactorizationMonoid
open SumProduct
variable {K : Type*} [Field K] [NumberField K]
namespace SumProduct
theorem _root_.solution {m n : ℕ} (hmn : Nat.Coprime m n) (hm : m ≠ 0) (hn : n ≠ 0) :
    idealCount K (m * n) = idealCount K m * idealCount K n := by
  rw [idealCount, idealCount, idealCount, ← Nat.card_prod]
  refine Nat.card_congr (Equiv.ofBijective
    (fun p : {I : Ideal (𝓞 K) // Ideal.absNorm I = m} × {J : Ideal (𝓞 K) // Ideal.absNorm J = n} =>
      (⟨p.1.1 * p.2.1, by rw [map_mul, p.1.2, p.2.2]⟩ :
        {L : Ideal (𝓞 K) // Ideal.absNorm L = m * n})) ⟨?_, ?_⟩).symm
  · rintro ⟨⟨I, hI⟩, ⟨J, hJ⟩⟩ ⟨⟨I', hI'⟩, ⟨J', hJ'⟩⟩ heq
    simp only [Subtype.mk_eq_mk] at heq
    have hI0 : I ≠ 0 := fun h => hm (by rw [← hI, h, Ideal.zero_eq_bot, Ideal.absNorm_bot])
    have hcop : IsCoprime I J' := isCoprime_of_coprime_absNorm (by rw [hI, hJ']; exact hmn)
    have hcop' : IsCoprime I' J := isCoprime_of_coprime_absNorm (by rw [hI', hJ]; exact hmn)
    have hII' : I = I' :=
      dvd_antisymm (hcop.dvd_of_dvd_mul_right (heq ▸ dvd_mul_right I J))
        (hcop'.dvd_of_dvd_mul_right (heq.symm ▸ dvd_mul_right I' J'))
    have hJJ' : J = J' := by
      rw [hII'] at heq; exact mul_left_cancel₀ (hII' ▸ hI0) heq
    simp only [Prod.mk_inj, Subtype.mk_eq_mk]; exact ⟨hII', hJJ'⟩
  · rintro ⟨L, hL⟩
    obtain ⟨I, J, hI, hJ, hIJ⟩ := exists_split hmn hm hn hL
    exact ⟨(⟨I, hI⟩, ⟨J, hJ⟩), by simp only [Subtype.mk_eq_mk]; exact hIJ⟩
end SumProduct

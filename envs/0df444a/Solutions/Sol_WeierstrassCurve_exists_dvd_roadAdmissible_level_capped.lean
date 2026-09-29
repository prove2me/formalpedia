-- Prove2me | solution 1 for WeierstrassCurve.exists_dvd_roadAdmissible_level_capped
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/3e5ad1fb-9d60-5f6f-bab4-229eb672f217

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_dvd_roadAdmissible_level_capped

private lemma roadLevelCapped_aux (e p : ℕ) (hp : p.Prime)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S)
    (M : ℕ) (hM0 : M ≠ 0) (hMS : ∀ q : ℕ, q.Prime → q ∣ M → q ∈ S)
    (ε : ℕ) (hεM : M.factorization p ≤ ε) :
    ∃ N : ℕ, M ∣ N ∧ N ≠ 0 ∧ (∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) ∧
      (∀ q ∈ S, q ≠ p → q ^ e ∣ N) ∧
      (∀ q ∈ S, q ≠ p → N.factorization q = max e (M.factorization q)) ∧ N.factorization p = ε := by
  classical
  set m : ℕ → ℕ := fun q => max e (M.factorization q) with hm
  have hprime_of_mem : ∀ q ∈ S.erase p, q.Prime :=
    fun q hq => hS q (Finset.mem_of_mem_erase hq)
  have hP0 : (∏ q ∈ S.erase p, q ^ m q) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun q hq => pow_ne_zero _ (hprime_of_mem q hq).ne_zero
  have hN0 : p ^ ε * ∏ q ∈ S.erase p, q ^ m q ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hp.ne_zero) hP0
  have hfact : ∀ r : ℕ,
      (p ^ ε * ∏ q ∈ S.erase p, q ^ m q).factorization r
        = (if p = r then ε else 0) + (if r ∈ S.erase p then m r else 0) := by
    intro r
    rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hP0, hp.factorization_pow,
      Nat.factorization_prod fun q hq => pow_ne_zero _ (hprime_of_mem q hq).ne_zero]
    have hsum : (∑ q ∈ S.erase p, (q ^ m q).factorization) r
        = ∑ q ∈ S.erase p, (if q = r then m q else 0) := by
      rw [Finsupp.finsetSum_apply]
      exact Finset.sum_congr rfl fun q hq => by
        rw [(hprime_of_mem q hq).factorization_pow, Finsupp.single_apply]
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, hsum,
      Finset.sum_ite_eq' (S.erase p) r m]
  refine ⟨p ^ ε * ∏ q ∈ S.erase p, q ^ m q, ?_, hN0, ?_, ?_, ?_, ?_⟩
  · rw [← Nat.factorization_le_iff_dvd hM0 hN0, Finsupp.le_def]
    intro r
    by_cases hr0 : M.factorization r = 0
    · simp [hr0]
    · have hrsupp : r ∈ M.factorization.support := Finsupp.mem_support_iff.mpr hr0
      rw [Nat.support_factorization] at hrsupp
      have hrS : r ∈ S :=
        hMS r (Nat.prime_of_mem_primeFactors hrsupp) (Nat.dvd_of_mem_primeFactors hrsupp)
      rw [hfact r]
      by_cases hrp : r = p
      · subst hrp
        simpa using hεM
      · have hrme : r ∈ S.erase p := Finset.mem_erase.mpr ⟨hrp, hrS⟩
        rw [if_neg (fun h : p = r => hrp h.symm), if_pos hrme, zero_add]
        exact le_max_right _ _
  · intro q hq hqN
    by_contra hqS
    have h1 : 1 ≤ (p ^ ε * ∏ q ∈ S.erase p, q ^ m q).factorization q := by
      rw [← hq.pow_dvd_iff_le_factorization hN0, pow_one]
      exact hqN
    rw [hfact q, if_neg (fun h : p = q => hqS (h ▸ hpS)),
      if_neg (fun h => hqS (Finset.mem_of_mem_erase h))] at h1
    omega
  · intro q hqS hqp
    have hq : q ∈ S.erase p := Finset.mem_erase.mpr ⟨hqp, hqS⟩
    rw [(hS q hqS).pow_dvd_iff_le_factorization hN0, hfact q, if_pos hq]
    exact le_add_left (le_max_left _ _)
  · intro q hqS hqp
    have hq : q ∈ S.erase p := Finset.mem_erase.mpr ⟨hqp, hqS⟩
    rw [hfact q, if_neg (fun h : p = q => hqp h.symm), if_pos hq, zero_add]
  · rw [hfact p, if_pos rfl, if_neg (Finset.notMem_erase p S), add_zero]

theorem solution (e : ℕ) (p : ℕ) (W : WeierstrassCurve ℤ)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S)
    (hbadS : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ W.Δ → q ∈ S)
    (M : ℕ) (hM : NeZero M) (hMS : ∀ q : ℕ, q.Prime → q ∣ M → q ∈ S)
    (hMe : ∀ q ∈ S, q ≠ p → ¬ q ^ (e + 1) ∣ M)
    (hMp_ord : (¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p) → ¬ p ^ 2 ∣ M)
    (hMp_flat : W.IsGoodPrimeFor p → (p : ℤ) ∣ W.apOfModel p → ¬ p ∣ M) :
    ∃ N : ℕ, M ∣ N ∧ N ≠ 0 ∧
      (∀ q ∈ S, q.Prime) ∧ p ∈ S ∧
      (∀ q : ℕ, q.Prime → (q : ℤ) ∣ W.Δ → q ∈ S) ∧
      (∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) ∧
      (∀ q ∈ S, q ≠ p → q ^ e ∣ N) ∧
      (∀ q ∈ S, q ≠ p → ¬ q ^ (e + 1) ∣ N) ∧
      ((¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p) → p ∣ N ∧ ¬ p ^ 2 ∣ N) ∧
      (W.IsGoodPrimeFor p → (p : ℤ) ∣ W.apOfModel p → ¬ p ∣ N) := by
  have hp : p.Prime := hS p hpS
  have hM0 : M ≠ 0 := hM.out

  have hcap : ∀ N : ℕ, N ≠ 0 → (∀ q ∈ S, q ≠ p → N.factorization q = max e (M.factorization q)) →
      ∀ q ∈ S, q ≠ p → ¬ q ^ (e + 1) ∣ N := by
    intro N hN0 hNfac q hqS hqp h
    have hq : q.Prime := hS q hqS
    have h1 : e + 1 ≤ N.factorization q := (hq.pow_dvd_iff_le_factorization hN0).mp h
    have h2 : M.factorization q ≤ e := by
      by_contra h'
      exact hMe q hqS hqp ((hq.pow_dvd_iff_le_factorization hM0).mpr (by omega))
    have h3 : max e (M.factorization q) ≤ e := max_le le_rfl h2
    rw [hNfac q hqS hqp] at h1
    omega
  by_cases hflat : W.IsGoodPrimeFor p ∧ (p : ℤ) ∣ W.apOfModel p
  · have hpM : ¬ p ∣ M := hMp_flat hflat.1 hflat.2
    obtain ⟨N, hMN, hN0, hNsupp, hNe, hNfac, hNp⟩ :=
      roadLevelCapped_aux e p hp S hS hpS M hM0 hMS 0
        (le_of_eq (Nat.factorization_eq_zero_of_not_dvd hpM))
    refine ⟨N, hMN, hN0, hS, hpS, hbadS, hNsupp, hNe, hcap N hN0 hNfac, ?_, ?_⟩
    · intro h
      rcases h with h | h
      · exact absurd hflat.1 h
      · exact absurd hflat.2 h
    · intro _ _ hpN
      have h1 : 1 ≤ N.factorization p := by
        rw [← hp.pow_dvd_iff_le_factorization hN0, pow_one]
        exact hpN
      omega
  · have hord : ¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p := not_and_or.mp hflat
    have hp2M : ¬ p ^ 2 ∣ M := hMp_ord hord
    have heps : M.factorization p ≤ 1 := by
      by_contra h
      exact hp2M (hp.pow_dvd_iff_le_factorization hM0 |>.mpr (by omega))
    obtain ⟨N, hMN, hN0, hNsupp, hNe, hNfac, hNp⟩ :=
      roadLevelCapped_aux e p hp S hS hpS M hM0 hMS 1 heps
    refine ⟨N, hMN, hN0, hS, hpS, hbadS, hNsupp, hNe, hcap N hN0 hNfac, ?_, ?_⟩
    · intro _
      constructor
      · rw [← pow_one p]
        exact (hp.pow_dvd_iff_le_factorization hN0).mpr (le_of_eq hNp.symm)
      · intro hp2N
        have h2 : 2 ≤ N.factorization p :=
          (hp.pow_dvd_iff_le_factorization hN0).mp hp2N
        omega
    · intro hGood hap
      exact absurd ⟨hGood, hap⟩ hflat

end S_WeierstrassCurve_exists_dvd_roadAdmissible_level_capped
end P2MW
export P2MW.S_WeierstrassCurve_exists_dvd_roadAdmissible_level_capped (solution)

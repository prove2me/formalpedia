-- Prove2me | solution 1 for TaoFivePrimes.smoothedExpSum_modulus_change
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-13T20:25:05.462605+00:00
-- url     : https://prove2.me/submissions/40982145-94a5-4832-ab7a-3ab9fe72246c

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace EtaSmash

/-- On a prime power `n` divisible by the prime `p`, von Mangoldt is `log p`. -/
theorem vonMangoldt_of_primePow_dvd {n p : ℕ} (hp : p.Prime) (hn : IsPrimePow n)
    (hdvd : p ∣ n) : (Λ n : ℝ) = Real.log p := by
  have hmin : n.minFac = p := by
    obtain ⟨q, k, hq, hk, rfl⟩ := hn
    have hqp : Nat.Prime q := hq.nat_prime
    have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqp).mp
      (hp.dvd_of_dvd_pow hdvd)
    subst hpq
    exact Nat.Prime.pow_minFac hp (by omega)
  rw [ArithmeticFunction.vonMangoldt_apply, if_pos hn, hmin]

/-- **Tao, Lemma 4.1 (the arithmetic core).**  The prime mass carried by the integers up to `N`
that are *not* coprime to `q₀` is at most `ω(q₀) log N`. -/
theorem sum_vonMangoldt_not_coprime_le (q₀ N : ℕ) (hq : 0 < q₀) (hN : 1 ≤ N) :
    ∑ n ∈ (Finset.range (N+1)).filter (fun n => ¬ Nat.Coprime n q₀), (Λ n : ℝ)
      ≤ (q₀.primeFactors.card : ℝ) * Real.log N := by
  classical
  set T : ℕ → Finset ℕ := fun p =>
    (Finset.range (N+1)).filter (fun n => IsPrimePow n ∧ p ∣ n) with hT
  -- drop the vanishing terms
  have hstep1 :
      ∑ n ∈ (Finset.range (N+1)).filter (fun n => ¬ Nat.Coprime n q₀), (Λ n : ℝ)
        = ∑ n ∈ ((Finset.range (N+1)).filter (fun n => ¬ Nat.Coprime n q₀)).filter
              (fun n => (Λ n : ℝ) ≠ 0), (Λ n : ℝ) :=
    (Finset.sum_filter_ne_zero _).symm
  -- the surviving terms live in the disjoint union of the `T p`
  have hsub : ((Finset.range (N+1)).filter (fun n => ¬ Nat.Coprime n q₀)).filter
      (fun n => (Λ n : ℝ) ≠ 0) ⊆ q₀.primeFactors.biUnion T := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨⟨hlt, hcop⟩, hne⟩ := hn
    have hpp : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hne
    -- the (unique) prime factor of `n` divides `q₀`
    set p := n.minFac with hp_def
    have hn1 : n ≠ 1 := by rintro rfl; exact absurd (Nat.coprime_one_left q₀) hcop
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact absurd (by simpa using hpp) (by simp [IsPrimePow])
    have hpprime : p.Prime := Nat.minFac_prime hn1
    have hpn : p ∣ n := Nat.minFac_dvd n
    have hpq : p ∣ q₀ := by
      obtain ⟨q, k, hq', hk, hnk⟩ := hpp
      have hqp : Nat.Prime q := hq'.nat_prime
      have hgcd : n.gcd q₀ ≠ 1 := hcop
      have hd : ∃ r, r.Prime ∧ r ∣ n ∧ r ∣ q₀ := by
        obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hgcd
        exact ⟨r, hr, hrd.trans (Nat.gcd_dvd_left _ _), hrd.trans (Nat.gcd_dvd_right _ _)⟩
      obtain ⟨r, hr, hrn, hrq⟩ := hd
      have : r = q := by
        refine (Nat.prime_dvd_prime_iff_eq hr hqp).mp ?_
        exact hr.dvd_of_dvd_pow (hnk ▸ hrn)
      have hpq' : p = q := by
        refine (Nat.prime_dvd_prime_iff_eq hpprime hqp).mp ?_
        exact hpprime.dvd_of_dvd_pow (hnk ▸ hpn)
      rw [hpq', ← this]; exact hrq
    refine Finset.mem_biUnion.mpr ⟨p, ?_, ?_⟩
    · exact Nat.mem_primeFactors.mpr ⟨hpprime, hpq, hq.ne'⟩
    · simp only [hT, Finset.mem_filter, Finset.mem_range]
      exact ⟨hlt, hpp, hpn⟩
  have hnn : ∀ n : ℕ, (0:ℝ) ≤ (Λ n : ℝ) := fun _ => ArithmeticFunction.vonMangoldt_nonneg
  have hstep2 :
      ∑ n ∈ ((Finset.range (N+1)).filter (fun n => ¬ Nat.Coprime n q₀)).filter
          (fun n => (Λ n : ℝ) ≠ 0), (Λ n : ℝ)
        ≤ ∑ n ∈ q₀.primeFactors.biUnion T, (Λ n : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hnn n)
  -- the `T p` are pairwise disjoint: a prime power has only one prime factor
  have hdisj : (q₀.primeFactors : Set ℕ).PairwiseDisjoint T := by
    intro p hp q hq hpq
    simp only [Finset.disjoint_left, hT, Finset.mem_filter, Finset.mem_range]
    rintro n ⟨-, hpp, hpn⟩ ⟨-, -, hqn⟩
    obtain ⟨r, k, hr, hk, hnk⟩ := hpp
    have hrp : Nat.Prime r := hr.nat_prime
    have hp' : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
    have hq' : Nat.Prime q := (Nat.mem_primeFactors.mp hq).1
    have e1 : p = r := (Nat.prime_dvd_prime_iff_eq hp' hrp).mp (hp'.dvd_of_dvd_pow (hnk ▸ hpn))
    have e2 : q = r := (Nat.prime_dvd_prime_iff_eq hq' hrp).mp (hq'.dvd_of_dvd_pow (hnk ▸ hqn))
    exact hpq (e1.trans e2.symm)
  rw [Finset.sum_biUnion hdisj] at hstep2
  -- each block contributes at most `log N`
  have hblock : ∀ p ∈ q₀.primeFactors, ∑ n ∈ T p, (Λ n : ℝ) ≤ Real.log N := by
    intro p hp
    have hp' : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
    have hp1 : 1 < p := hp'.one_lt
    have hval : ∀ n ∈ T p, (Λ n : ℝ) = Real.log p := by
      intro n hn
      simp only [hT, Finset.mem_filter, Finset.mem_range] at hn
      exact vonMangoldt_of_primePow_dvd hp' hn.2.1 hn.2.2
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
    -- the block has at most `log_p N` elements
    have hcard : (T p).card ≤ Nat.log p N := by
      have himg : T p ⊆ (Finset.Icc 1 (Nat.log p N)).image (fun k => p ^ k) := by
        intro n hn
        simp only [hT, Finset.mem_filter, Finset.mem_range] at hn
        obtain ⟨hlt, hpp, hpn⟩ := hn
        obtain ⟨r, k, hr, hk, hnk⟩ := hpp
        have hrp : Nat.Prime r := hr.nat_prime
        have e1 : p = r := (Nat.prime_dvd_prime_iff_eq hp' hrp).mp (hp'.dvd_of_dvd_pow (hnk ▸ hpn))
        refine Finset.mem_image.mpr ⟨k, ?_, ?_⟩
        · refine Finset.mem_Icc.mpr ⟨hk, ?_⟩
          rw [Nat.le_log_iff_pow_le hp1 (by omega)]
          calc p ^ k = r ^ k := by rw [e1]
            _ = n := hnk
            _ ≤ N := by omega
        · rw [e1]; exact hnk
      calc (T p).card ≤ ((Finset.Icc 1 (Nat.log p N)).image (fun k => p ^ k)).card :=
            Finset.card_le_card himg
        _ ≤ (Finset.Icc 1 (Nat.log p N)).card := Finset.card_image_le
        _ = Nat.log p N := by rw [Nat.card_Icc]; omega
    have hlogp : (0:ℝ) < Real.log p := Real.log_pos (by exact_mod_cast hp1)
    have hpow : (p : ℝ) ^ (Nat.log p N) ≤ (N : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self p (by omega)
    calc ((T p).card : ℝ) * Real.log p ≤ (Nat.log p N : ℝ) * Real.log p := by
          have : ((T p).card : ℝ) ≤ (Nat.log p N : ℝ) := by exact_mod_cast hcard
          nlinarith
      _ = Real.log ((p : ℝ) ^ (Nat.log p N)) := by rw [Real.log_pow]
      _ ≤ Real.log N := Real.log_le_log (by positivity) hpow
  calc ∑ n ∈ (Finset.range (N+1)).filter (fun n => ¬ Nat.Coprime n q₀), (Λ n : ℝ)
      = _ := hstep1
    _ ≤ ∑ p ∈ q₀.primeFactors, ∑ n ∈ T p, (Λ n : ℝ) := hstep2
    _ ≤ ∑ p ∈ q₀.primeFactors, Real.log N := Finset.sum_le_sum hblock
    _ = (q₀.primeFactors.card : ℝ) * Real.log N := by
        rw [Finset.sum_const, nsmul_eq_mul]


open TaoFivePrimes

theorem norm_expCircle (θ : ℝ) : ‖expCircle θ‖ = 1 := by
  unfold expCircle
  rw [Complex.norm_exp]
  norm_num


/-- **Tao, Lemma 4.1.**  `S_{η,q₀}(x,α) = S_{η,1}(x,α) + O*(ω(q₀) ‖η‖_∞ log x)`:
the smoothed prime exponential sum barely depends on the sifting modulus `q₀`. -/
theorem smoothedExpSum_modulus_change (η : ℝ → ℝ) (M : ℝ) (q₀ : ℕ) (x α : ℝ)
    (hq : 0 < q₀) (hx : 1 ≤ x)
    (hM : ∀ t : ℝ, |η t| ≤ M)
    (hsupp : ∀ t : ℝ, 1 < t → η t = 0) :
    ‖smoothedExpSum η q₀ x α - smoothedExpSum η 1 x α‖
      ≤ (q₀.primeFactors.card : ℝ) * M * Real.log x := by
  classical
  have hx0 : (0:ℝ) < x := by linarith
  set N : ℕ := ⌊x⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hvanish : ∀ n : ℕ, n ∉ Finset.range (N+1) → η ((n : ℝ) / x) = 0 := by
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    refine hsupp _ ?_
    rw [lt_div_iff₀ hx0, one_mul]
    have h1 : (N : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 := Nat.lt_floor_add_one x
    rw [← hN] at h2
    linarith
  set Tm : ℕ → ℂ := fun n => (Λ n : ℂ) * expCircle (α * n) * (η ((n : ℝ) / x) : ℂ) with hTm
  have hsum : ∀ q : ℕ, smoothedExpSum η q x α
      = ∑ n ∈ Finset.range (N+1), (if Nat.Coprime n q then Tm n else 0) := by
    intro q
    refine tsum_eq_sum ?_
    intro n hn
    by_cases h : Nat.Coprime n q
    · rw [if_pos h]
      simp [hvanish n hn]
    · rw [if_neg h]
  rw [hsum q₀, hsum 1]
  have hone : ∀ n : ℕ, (if Nat.Coprime n 1 then Tm n else 0) = Tm n := by
    intro n; rw [if_pos (Nat.coprime_one_right n)]
  simp only [hone]
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ n ∈ Finset.range (N+1),
      (if Nat.Coprime n q₀ then Tm n else 0) - Tm n
        = (if ¬ Nat.Coprime n q₀ then -Tm n else 0) := by
    intro n _
    by_cases h : Nat.Coprime n q₀
    · rw [if_pos h, if_neg (by simpa using h)]; ring
    · rw [if_neg h, if_pos h]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  refine le_trans (norm_sum_le _ _) ?_
  have hbd : ∀ n ∈ (Finset.range (N+1)).filter (fun n => ¬ Nat.Coprime n q₀),
      ‖-Tm n‖ ≤ (Λ n : ℝ) * M := by
    intro n _
    rw [norm_neg, hTm]
    simp only [norm_mul, Complex.norm_natCast, norm_expCircle, mul_one]
    have h1 : ‖((Λ n : ℝ) : ℂ)‖ = (Λ n : ℝ) := by
      rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have h2 : ‖((η ((n:ℝ)/x) : ℝ) : ℂ)‖ ≤ M := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hM _
    calc ‖((Λ n : ℝ) : ℂ)‖ * ‖((η ((n:ℝ)/x) : ℝ) : ℂ)‖
        = (Λ n : ℝ) * ‖((η ((n:ℝ)/x) : ℝ) : ℂ)‖ := by rw [h1]
      _ ≤ (Λ n : ℝ) * M := by
          exact mul_le_mul_of_nonneg_left h2 ArithmeticFunction.vonMangoldt_nonneg
  refine le_trans (Finset.sum_le_sum hbd) ?_
  rw [← Finset.sum_mul]
  have hMnn : (0:ℝ) ≤ M := le_trans (abs_nonneg _) (hM 0)
  have harith := sum_vonMangoldt_not_coprime_le q₀ N hq hN1
  have hlogN : Real.log (N : ℝ) ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast hN1) (Nat.floor_le hx0.le)
  have hlogN0 : (0:ℝ) ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  have hcard : (0:ℝ) ≤ (q₀.primeFactors.card : ℝ) := Nat.cast_nonneg _
  calc (∑ n ∈ (Finset.range (N+1)).filter (fun n => ¬ Nat.Coprime n q₀), (Λ n : ℝ)) * M
      ≤ ((q₀.primeFactors.card : ℝ) * Real.log (N:ℝ)) * M :=
        mul_le_mul_of_nonneg_right harith hMnn
    _ ≤ ((q₀.primeFactors.card : ℝ) * Real.log x) * M := by
        have hprod : (0:ℝ) ≤ ((q₀.primeFactors.card : ℝ) * M) * (Real.log x - Real.log (N:ℝ)) :=
          mul_nonneg (mul_nonneg hcard hMnn) (by linarith)
        nlinarith [hprod]
    _ = (q₀.primeFactors.card : ℝ) * M * Real.log x := by ring

end EtaSmash

theorem solution (eta : ℝ → ℝ) (M : ℝ) (q₀ : ℕ) (x alpha : ℝ)
    (hq : 0 < q₀) (hx : 1 ≤ x)
    (hM : ∀ t : ℝ, |eta t| ≤ M)
    (hsupp : ∀ t : ℝ, 1 < t → eta t = 0) :
    ‖TaoFivePrimes.smoothedExpSum eta q₀ x alpha
        - TaoFivePrimes.smoothedExpSum eta 1 x alpha‖
      ≤ (q₀.primeFactors.card : ℝ) * M * Real.log x :=
  EtaSmash.smoothedExpSum_modulus_change eta M q₀ x alpha hq hx hM hsupp

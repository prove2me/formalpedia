-- Prove2me | solution 1 for TaoFivePrimes.log_le_sum_moebius_sq_div_totient
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-14T01:06:22.279902+00:00
-- url     : https://prove2.me/submissions/2e2c1153-483d-4910-801e-da31f4c22485

import Mathlib

open Finset

namespace TaoGR

/-- The radical of `n`: the product of its distinct prime factors. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

theorem rad_pos (n : ℕ) : 0 < rad n := by
  rw [rad]
  refine Finset.prod_pos (fun p hp => ?_)
  exact (Nat.prime_of_mem_primeFactors hp).pos

theorem rad_squarefree (n : ℕ) : Squarefree (rad n) := by
  rw [rad]
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun a ha b hb hab => ?_)
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).squarefree)
  simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors ha)
    (Nat.prime_of_mem_primeFactors hb)).mpr hab

theorem primeFactors_rad (n : ℕ) : (rad n).primeFactors = n.primeFactors :=
  Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors hp)

theorem rad_dvd (n : ℕ) : rad n ∣ n := Nat.prod_primeFactors_dvd n

theorem rad_le (n : ℕ) (hn : n ≠ 0) : rad n ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (rad_dvd n)

theorem rad_eq_one_iff {n : ℕ} (hn : n ≠ 0) : rad n = 1 ↔ n = 1 := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨p, hp⟩ := (Nat.nonempty_primeFactors (n := n)).mpr (by omega)
    have : p ∣ rad n := Finset.dvd_prod_of_mem _ hp
    rw [h, Nat.dvd_one] at this
    exact (Nat.prime_of_mem_primeFactors hp).ne_one this
  · rintro rfl
    simp [rad]

theorem rad_ordCompl {n p : ℕ} (hn : n ≠ 0) (hp : p ∈ n.primeFactors) :
    rad (n / p ^ n.factorization p) = rad n / p := by
  have hfac : (n / p ^ n.factorization p).primeFactors = n.primeFactors.erase p := by
    have := Nat.factorization_ordCompl n p
    rw [← Nat.support_factorization, this, Finsupp.support_erase, Nat.support_factorization]
  rw [rad, rad, hfac, ← Finset.prod_erase_mul _ _ hp]
  rw [Nat.mul_div_cancel]
  exact (Nat.prime_of_mem_primeFactors hp).pos

theorem geom_sum_inv {p : ℕ} (hp : 2 ≤ p) (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / (p : ℝ) ^ k)
      = (1 - (1 / (p : ℝ)) ^ K) / ((p : ℝ) - 1) := by
  have hp2 : (2:ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0:ℝ) < (p : ℝ) := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  induction K with
  | zero => simp
  | succ K IH =>
    rw [Finset.sum_Icc_succ_top (by omega), IH]
    have hpK : ((p : ℝ)) ^ K ≠ 0 := by positivity
    simp only [div_pow, one_pow]
    field_simp
    ring

theorem geom_bound {p : ℕ} (hp : 2 ≤ p) (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / (p : ℝ) ^ k) ≤ 1 / ((p : ℝ) - 1) := by
  have hp2 : (2:ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  rw [geom_sum_inv hp K]
  have h1 : (0:ℝ) ≤ (1 / (p : ℝ)) ^ K := by positivity
  have h2 : (0:ℝ) < (p : ℝ) - 1 := by linarith
  rw [div_le_div_iff_of_pos_right h2]
  linarith


/-- For a squarefree `q`, the integers with radical `q` have reciprocal sum at most
`1/φ(q)`, uniformly over finite subsets. -/
theorem fibre_bound : ∀ q : ℕ, Squarefree q → ∀ S : Finset ℕ,
    (∀ n ∈ S, n ≠ 0 ∧ rad n = q) →
    (∑ n ∈ S, (1 : ℝ) / n) ≤ 1 / (Nat.totient q : ℝ) := by
  classical
  intro q
  induction q using Nat.strong_induction_on with
  | _ q IH =>
    intro hsf S hS
    have hq0 : q ≠ 0 := hsf.ne_zero
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hq0) with h1 | h1
    · -- `q = 1`
      have hq1 : q = 1 := h1.symm
      subst hq1
      have hsub : S ⊆ {1} := by
        intro n hn
        obtain ⟨hn0, hrad⟩ := hS n hn
        simp only [Finset.mem_singleton]
        exact (rad_eq_one_iff hn0).mp hrad
      have : (∑ n ∈ S, (1:ℝ)/n) ≤ ∑ n ∈ ({1} : Finset ℕ), (1:ℝ)/n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
      simpa using this
    · -- `q > 1`
      set p : ℕ := q.minFac with hpdef
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have hpq : p ∣ q := Nat.minFac_dvd q
      set q' : ℕ := q / p with hq'def
      have hpq' : p * q' = q := Nat.mul_div_cancel' hpq
      have hnpq' : ¬ p ∣ q' := by
        intro hd
        obtain ⟨t, ht⟩ := hd
        exact hp.not_isUnit (hsf p ⟨t, by rw [← hpq', ht]; ring⟩)
      have hcop : Nat.Coprime p q' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnpq'
      have hq'dvd : q' ∣ q := ⟨p, by rw [← hpq']; ring⟩
      have hsf' : Squarefree q' := hsf.squarefree_of_dvd hq'dvd
      have hq'0 : q' ≠ 0 := hsf'.ne_zero
      have hq'lt : q' < q := by
        have := hp.one_lt
        calc q' = 1 * q' := (one_mul q').symm
          _ < p * q' := (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero hq'0)).mpr this
          _ = q := hpq'
      -- every `n` in `S` is divisible by `p`
      have hmemp : ∀ n ∈ S, p ∈ n.primeFactors := by
        intro n hn
        obtain ⟨hn0, hrad⟩ := hS n hn
        refine Nat.mem_primeFactors.mpr ⟨hp, ?_, hn0⟩
        exact dvd_trans (hrad ▸ hpq) (rad_dvd n)
      set K : ℕ := S.sup (fun n => n.factorization p) with hK
      have hmaps : ∀ n ∈ S, n.factorization p ∈ Finset.Icc 1 K := by
        intro n hn
        refine Finset.mem_Icc.mpr ⟨?_, Finset.le_sup (f := fun n => n.factorization p) hn⟩
        have := hmemp n hn
        rw [Nat.mem_primeFactors] at this
        exact (Nat.Prime.factorization_pos_of_dvd hp this.2.2 this.2.1)
      rw [← Finset.sum_fiberwise_of_maps_to hmaps]
      -- each fibre
      have hfib : ∀ k ∈ Finset.Icc 1 K,
          (∑ n ∈ S.filter (fun n => n.factorization p = k), (1:ℝ)/n)
            ≤ (1/(p:ℝ)^k) * (1 / (Nat.totient q' : ℝ)) := by
        intro k _
        set T : Finset ℕ := S.filter (fun n => n.factorization p = k) with hT
        have hTmem : ∀ n ∈ T, n ≠ 0 ∧ rad n = q ∧ n.factorization p = k := by
          intro n hn
          rw [hT, Finset.mem_filter] at hn
          exact ⟨(hS n hn.1).1, (hS n hn.1).2, hn.2⟩
        have hrecover : ∀ n ∈ T, p ^ k * (n / p ^ k) = n := by
          intro n hn
          obtain ⟨_, _, hk⟩ := hTmem n hn
          rw [← hk]
          exact Nat.ordProj_mul_ordCompl_eq_self n p
        have hinj : ∀ n ∈ T, ∀ n' ∈ T, n / p ^ k = n' / p ^ k → n = n' := by
          intro n hn n' hn' h
          rw [← hrecover n hn, ← hrecover n' hn', h]
        have himg : ∀ m ∈ T.image (fun n => n / p ^ k), m ≠ 0 ∧ rad m = q' := by
          intro m hm
          obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
          obtain ⟨hn0, hrad, hk⟩ := hTmem n hn
          rw [← hk]
          refine ⟨(Nat.ordCompl_pos p hn0).ne', ?_⟩
          rw [rad_ordCompl hn0 (hmemp n (Finset.mem_of_mem_filter n hn)), hrad, hq'def]
        have hIH := IH q' hq'lt hsf' (T.image (fun n => n / p ^ k))
          (fun m hm => himg m hm)
        have hsplit : (∑ n ∈ T, (1:ℝ)/n)
            = (1/(p:ℝ)^k) * ∑ m ∈ T.image (fun n => n / p ^ k), (1:ℝ)/m := by
          rw [Finset.sum_image hinj, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun n hn => ?_)
          have hrec := hrecover n hn
          have hppos : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
          have hpk : ((p:ℝ)) ^ k ≠ 0 := by positivity
          have hcast : ((n : ℕ) : ℝ) = ((p:ℝ) ^ k) * ((n / p ^ k : ℕ) : ℝ) := by
            have := congrArg (fun t : ℕ => (t : ℝ)) hrec
            push_cast at this
            linarith [this]
          rw [hcast]
          field_simp
        rw [hsplit]
        have hpk0 : (0:ℝ) < (1/(p:ℝ)^k) := by
          have : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
          positivity
        exact mul_le_mul_of_nonneg_left hIH (le_of_lt hpk0)
      refine le_trans (Finset.sum_le_sum hfib) ?_
      rw [← Finset.sum_mul]
      have hphi' : (0:ℝ) ≤ 1 / (Nat.totient q' : ℝ) := by positivity
      have hgeo := geom_bound (p := p) hp.two_le K
      have hstep : (∑ k ∈ Finset.Icc 1 K, (1:ℝ)/(p:ℝ)^k) * (1 / (Nat.totient q' : ℝ))
          ≤ (1 / ((p:ℝ) - 1)) * (1 / (Nat.totient q' : ℝ)) :=
        mul_le_mul_of_nonneg_right hgeo hphi'
      refine le_trans hstep (le_of_eq ?_)
      have hphi : (Nat.totient q : ℝ) = ((p:ℝ) - 1) * (Nat.totient q' : ℝ) := by
        rw [← hpq', Nat.totient_mul hcop, Nat.totient_prime hp, Nat.cast_mul,
          Nat.cast_sub hp.one_lt.le]
        push_cast
        ring
      rw [hphi]
      field_simp


/-- The harmonic sum is dominated by the totient sum. -/
theorem harmonic_le_totient_sum (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n)
      ≤ ∑ q ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ)) := by
  classical
  have hmaps : ∀ n ∈ Finset.Icc 1 N, rad n ∈ Finset.Icc 1 N := by
    intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    exact ⟨rad_pos n, le_trans (rad_le n (by omega)) hn.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum (fun q hq => ?_)
  set F : Finset ℕ := (Finset.Icc 1 N).filter (fun n => rad n = q) with hF
  rcases Finset.eq_empty_or_nonempty F with hemp | ⟨n₀, hn₀⟩
  · rw [hemp]
    simp only [Finset.sum_empty]
    positivity
  · have hn₀' : n₀ ∈ Finset.Icc 1 N ∧ rad n₀ = q := by
      rw [hF, Finset.mem_filter] at hn₀
      exact hn₀
    have hsf : Squarefree q := hn₀'.2 ▸ rad_squarefree n₀
    have hmu : ((ArithmeticFunction.moebius q : ℝ)) ^ 2 = 1 := by
      have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
    rw [hmu]
    refine fibre_bound q hsf F (fun n hn => ?_)
    rw [hF, Finset.mem_filter, Finset.mem_Icc] at hn
    exact ⟨by omega, hn.2⟩

/-- **The lower bound `G(R) ≥ log R` for the Montgomery–Vaughan totient sum.** -/
theorem G_ge_log (R : ℝ) (hR : 0 ≤ R) :
    Real.log R
      ≤ ∑ q ∈ Finset.Icc 1 ⌊R⌋₊,
          ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ)) := by
  refine le_trans (log_le_harmonic_floor R hR) ?_
  refine le_trans (le_of_eq ?_) (harmonic_le_totient_sum ⌊R⌋₊)
  rw [harmonic_eq_sum_Icc]
  push_cast
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [one_div]




end TaoGR

theorem solution (R : ℝ) (hR : 0 ≤ R) :
    Real.log R ≤ ∑ q ∈ Finset.Icc 1 ⌊R⌋₊,
      ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ)) :=
  TaoGR.G_ge_log R hR

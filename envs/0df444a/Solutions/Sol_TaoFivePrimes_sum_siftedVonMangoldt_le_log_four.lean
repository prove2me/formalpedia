-- Prove2me | solution 1 for TaoFivePrimes.sum_siftedVonMangoldt_le_log_four
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-12T16:39:13.142433+00:00
-- url     : https://prove2.me/submissions/8cbbbbe2-203c-4b29-b5ce-4f5c16d27e4a

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount

open TaoFivePrimes
open scoped ArithmeticFunction.vonMangoldt

private theorem sifted_prime {N n : ℕ} (hn : n ≤ N) (h : siftedVonMangoldt N n ≠ 0) :
    n.Prime := by
  unfold siftedVonMangoldt at h
  split at h
  · rename_i hcop
    obtain ⟨p, k, hp, hk, rfl⟩ := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h
    have hpn : p.Prime := Nat.prime_iff.mpr hp
    have hpdvd : p ∣ p ^ k := dvd_pow_self p hk.ne'
    have hbig : Nat.sqrt N < p := by
      by_contra hcon
      push_neg at hcon
      have hd : p ∣ primorial (Nat.sqrt N) := (Nat.Prime.dvd_primorial_iff hpn).2 hcon
      have hg : p ∣ Nat.gcd (p ^ k) (primorial (Nat.sqrt N)) := Nat.dvd_gcd hpdvd hd
      rw [hcop] at hg
      exact Nat.Prime.one_lt hpn |>.ne' (Nat.dvd_one.mp hg)
    have hk1 : k = 1 := by
      by_contra hk2
      have hk2' : 2 ≤ k := by omega
      have ha : (Nat.sqrt N + 1) * (Nat.sqrt N + 1) ≤ p * p := Nat.mul_le_mul hbig hbig
      have hb : p * p ≤ p ^ k := by
        calc p * p = p ^ 2 := by ring
          _ ≤ p ^ k := Nat.pow_le_pow_right hpn.pos hk2'
      have hc : N < (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := Nat.lt_succ_sqrt N
      omega
    subst hk1
    simpa using hpn
  · exact absurd rfl h

theorem solution (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), TaoFivePrimes.siftedVonMangoldt N n ≤ (N : ℝ) * Real.log 4 := by
  have hfilter : ∑ n ∈ (Finset.range (N + 1)).filter Nat.Prime, siftedVonMangoldt N n
      = ∑ n ∈ Finset.range (N + 1), siftedVonMangoldt N n := by
    refine Finset.sum_filter_of_ne ?_
    intro n hn hne
    exact sifted_prime (by simpa [Nat.lt_succ_iff] using hn) hne
  rw [← hfilter]
  have hle : ∀ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
      siftedVonMangoldt N p ≤ Real.log (p : ℝ) := by
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    unfold siftedVonMangoldt
    split
    · rw [ArithmeticFunction.vonMangoldt_apply_prime hpp]
    · exact Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
  have hprod : ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log (p : ℝ)
      = Real.log ((primorial N : ℕ) : ℝ) := by
    rw [primorial, Nat.cast_prod]
    refine (Real.log_prod ?_).symm
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    exact_mod_cast hpp.pos.ne'
  calc ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, siftedVonMangoldt N p
      ≤ ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log (p : ℝ) :=
        Finset.sum_le_sum hle
    _ = Real.log ((primorial N : ℕ) : ℝ) := hprod
    _ ≤ Real.log ((4 : ℝ) ^ N) := by
        refine Real.log_le_log (by exact_mod_cast (primorial_pos N)) ?_
        exact_mod_cast primorial_le_four_pow N
    _ = (N : ℝ) * Real.log 4 := by rw [Real.log_pow]

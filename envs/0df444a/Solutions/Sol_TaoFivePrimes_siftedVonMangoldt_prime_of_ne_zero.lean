-- Prove2me | solution 1 for TaoFivePrimes.siftedVonMangoldt_prime_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-12T16:39:12.539518+00:00
-- url     : https://prove2.me/submissions/e3644621-da58-4280-80fb-41da34412709

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount

open TaoFivePrimes
open scoped ArithmeticFunction.vonMangoldt

theorem solution {N n : ℕ} (hn : n ≤ N) (h : TaoFivePrimes.siftedVonMangoldt N n ≠ 0) :
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

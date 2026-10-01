-- Prove2me | solution 1 for Richstein2001.even_goldbach_up_to_4e14
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @webmh
-- created : 2026-09-11T23:28:27.457361+00:00
-- url     : https://prove2.me/submissions/ebe8dd2c-f282-4249-883c-20ad9bafa738
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Richstein2001_segmented_sieve_coverage
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxRecDepth 4096

namespace GoldbachSieve

/-- A complete sieve up to a square-root bound has no composite survivors. -/
theorem survivor_prime {lo hi cutoff q : ℕ}
    (hbound : hi ≤ cutoff ^ 2) (hq : q ∈ survivors lo hi cutoff) : q.Prime := by
  obtain ⟨hqrange, hsieve⟩ := Finset.mem_filter.mp hq
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hqrange
  have htwo : 2 ≤ q := le_trans (le_max_left _ _) hlo
  by_contra hnprime
  have hminprime := Nat.minFac_prime (show q ≠ 1 by omega)
  have hsq := Nat.minFac_sq_le_self (show 0 < q by omega) hnprime
  have hminle : q.minFac ≤ cutoff := by nlinarith
  have hminmem : q.minFac ∈ (Finset.Icc 2 cutoff).filter Nat.Prime :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hminprime.two_le, hminle⟩, hminprime⟩
  have hne : q.minFac ≠ q := by
    intro heq
    exact hnprime (heq ▸ hminprime)
  have hbad : q.minFac ∈ ((Finset.Icc 2 cutoff).filter Nat.Prime).filter
      (fun r => r ∣ q ∧ r ≠ q) :=
    Finset.mem_filter.mpr ⟨hminmem, Nat.minFac_dvd q, hne⟩
  have hempty := Finset.card_eq_zero.mp hsieve
  rw [hempty] at hbad
  exact Finset.notMem_empty _ hbad

/-- Every covered number is a sum of two primes once the sieve bound is complete. -/
theorem pairSums_sound {smallBound lo hi cutoff n : ℕ}
    (hbound : hi ≤ cutoff ^ 2) (hn : n ∈ pairSums smallBound lo hi cutoff) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  obtain ⟨p, hp, hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hn
  exact ⟨p, q, (Finset.mem_filter.mp hp).2, survivor_prime hbound hq, heq⟩

end GoldbachSieve

attribute [local irreducible] GoldbachSieve.pairSums GoldbachSieve.survivors

theorem solution (n : ℕ)
    (h4 : 4 ≤ n) (hN : n ≤ 4 * 10 ^ 14) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  let b := n / 1000000
  have hb : b < 400000001 := by dsimp [b]; omega
  have hlo : b * 1000000 ≤ n := Nat.div_mul_le_self n 1000000
  have hhi : n ≤ (b + 1) * 1000000 - 1 := by
    have hrem := Nat.mod_lt n (show 0 < 1000000 by decide)
    have hsplit := Nat.mod_add_div n 1000000
    dsimp [b]
    omega
  have hmem : n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun k => Even k)) := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨max_le h4 hlo, le_min hN hhi⟩, he⟩
  have hcovered := @Richstein2001.segmented_sieve_coverage b hb n hmem
  have hsquare : min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1) ≤ 20000000 ^ 2 := by
    calc
      min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1) ≤ 4 * 10 ^ 14 := min_le_left _ _
      _ ≤ 20000000 ^ 2 := by norm_num
  exact @GoldbachSieve.pairSums_sound 5569 (b * 1000000 - 5569)
    (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000 n hsquare hcovered

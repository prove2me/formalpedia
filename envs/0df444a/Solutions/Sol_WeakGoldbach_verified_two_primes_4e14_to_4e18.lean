-- Prove2me | solution 1 for WeakGoldbach.verified_two_primes_4e14_to_4e18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-15T13:50:35.465077+00:00
-- url     : https://prove2.me/submissions/7020cdba-e182-45ee-9d64-dd2512d4562c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Theorems.Thm_WeakGoldbach_verified_range_sieve_coverage
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

theorem solution (m : ℕ) (hlo : 4 * 10 ^ 14 < m)
    (hB : m ≤ 4 * 10 ^ 18) (he : Even m) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ m = p + q := by
  let b := (m - 4 * 10 ^ 14) / 1000000
  have hb : b < 4000000000001 := by
    have hm : m - 4 * 10 ^ 14 ≤ 4 * 10 ^ 18 - 4 * 10 ^ 14 := Nat.sub_le_sub_right hB _
    have h1 : b ≤ (4 * 10 ^ 18 - 4 * 10 ^ 14) / 1000000 := by
      dsimp [b]
      exact Nat.div_le_div_right hm
    have h2 : (4 * 10 ^ 18 - 4 * 10 ^ 14) / 1000000 = 3999600000000 := by norm_num
    omega
  have hlo' : 4 * 10 ^ 14 + b * 1000000 ≤ m := by
    have h1 : b * 1000000 ≤ m - 4 * 10 ^ 14 := by
      dsimp [b]
      exact Nat.div_mul_le_self _ _
    have h3 : 4 * 10 ^ 14 + (m - 4 * 10 ^ 14) = m := by omega
    calc
      4 * 10 ^ 14 + b * 1000000 ≤ 4 * 10 ^ 14 + (m - 4 * 10 ^ 14) :=
        Nat.add_le_add_left h1 _
      _ = m := h3
  have hhi' : m ≤ 4 * 10 ^ 14 + (b + 1) * 1000000 - 1 := by
    have hrem := Nat.mod_lt (m - 4 * 10 ^ 14) (show 0 < 1000000 by norm_num)
    have hsplit := Nat.mod_add_div (m - 4 * 10 ^ 14) 1000000
    dsimp [b]
    omega
  have hmem : m ∈ ((Finset.Icc (max 4 (4 * 10 ^ 14 + b * 1000000))
      (min (4 * 10 ^ 18) (4 * 10 ^ 14 + (b + 1) * 1000000 - 1))).filter
        (fun n => Even n)) := by
    have h4 : 4 ≤ m := by omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨max_le h4 hlo', le_min hB hhi'⟩, he⟩
  have hcovered := @WeakGoldbach.verified_range_sieve_coverage b hb m hmem
  have hsquare : min (4 * 10 ^ 18) (4 * 10 ^ 14 + (b + 1) * 1000000 - 1)
      ≤ 2000000000 ^ 2 := by
    calc
      min (4 * 10 ^ 18) (4 * 10 ^ 14 + (b + 1) * 1000000 - 1) ≤ 4 * 10 ^ 18 :=
        min_le_left _ _
      _ = 2000000000 ^ 2 := by norm_num
  obtain ⟨p, q, hp, hq, heq⟩ := GoldbachSieve.pairSums_sound hsquare hcovered
  exact ⟨p, q, hp, hq, heq.symm⟩

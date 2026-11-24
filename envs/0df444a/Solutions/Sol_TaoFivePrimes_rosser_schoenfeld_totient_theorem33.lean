-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_totient_theorem33
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T09:16:10.6817+00:00
-- url     : https://prove2.me/submissions/24045f3c-6da3-44ee-88ce-0818257485d2

import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_lemma14

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.Nth
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

namespace TaoFivePrimes

private lemma primesLE_eq_image_count (N : ℕ) :
    Nat.primesLE N =
      (Finset.range (Nat.count Nat.Prime (N + 1))).image (Nat.nth Nat.Prime) := by
  ext p
  rw [Nat.mem_primesLE, Finset.mem_image]
  constructor
  · rintro ⟨hple, hpprime⟩
    exact ⟨Nat.count Nat.Prime p,
      Finset.mem_range.mpr (Nat.count_strict_mono (p := Nat.Prime) hpprime (by omega)),
      Nat.nth_count hpprime⟩
  · rintro ⟨i, hi, rfl⟩
    have hlt : i < Nat.count Nat.Prime (N + 1) := Finset.mem_range.mp hi
    exact ⟨Nat.le_of_lt_succ (Nat.nth_lt_of_lt_count (p := Nat.Prime) (n := N + 1) hlt),
      Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime i⟩

/-- Rosser–Schoenfeld (1962), Theorem 33: the primorial-product bound for
`n/φ(n)` in terms of the Chebyshev theta function. -/
theorem solution (x : ℝ) (n : ℕ) (hx : 5 ≤ x) (hn : 1 ≤ n)
    (h : (n : ℝ) < Real.exp (Chebyshev.theta x)) :
    (n : ℝ) / Nat.totient n ≤
      ∏ p ∈ Nat.primesLE ⌊x - 2⌋₊, (p : ℝ) / ((p : ℝ) - 1) := by
  set k := Nat.count Nat.Prime (⌊x - 2⌋₊ + 1) with hk
  have hx22 : 2 ≤ ⌊x - 2⌋₊ := Nat.le_floor (by linarith : (2 : ℝ) ≤ x - 2)
  have hfloor_le : ⌊x⌋₊ ≤ ⌊x - 2⌋₊ + 2 := by
    have h1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
    have h2 : x - 2 < (⌊x - 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (x - 2)
    have h3 : (⌊x⌋₊ : ℝ) < (⌊x - 2⌋₊ : ℝ) + 3 := by linarith
    have h4 : ⌊x⌋₊ < ⌊x - 2⌋₊ + 3 := by exact_mod_cast h3
    omega
  have hk1 : 1 ≤ k := by
    rw [hk]
    have h' := Nat.count_strict_mono (p := Nat.Prime) Nat.prime_two (by omega :
      2 < ⌊x - 2⌋₊ + 1)
    omega
  have hkey : ∀ q : ℕ, Nat.Prime q → q ≤ ⌊x⌋₊ → q ≤ Nat.nth Nat.Prime k := by
    intro q hq hqle
    by_cases hqx2 : q ≤ ⌊x - 2⌋₊
    · have hqcnt : Nat.count Nat.Prime q < k := by
        rw [hk]
        exact Nat.count_strict_mono (p := Nat.Prime) hq (by omega)
      calc q = Nat.nth Nat.Prime (Nat.count Nat.Prime q) := (Nat.nth_count hq).symm
        _ ≤ Nat.nth Nat.Prime (k - 1) :=
            (Nat.nth_le_nth Nat.infinite_setOfPred_prime).mpr (by omega)
        _ ≤ Nat.nth Nat.Prime k := le_of_lt (by
            apply Nat.nth_lt_of_lt_count (p := Nat.Prime)
            rw [Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime]
            omega)
    · have hqlo : ⌊x - 2⌋₊ + 1 ≤ q := by omega
      have hqhi : q ≤ ⌊x - 2⌋₊ + 2 := by omega
      have hle2 : Nat.nth Nat.Prime k ≤ q := by
        by_contra hcon
        push_neg at hcon
        have h1 : Nat.count Nat.Prime q < Nat.count Nat.Prime (Nat.nth Nat.Prime k) :=
          Nat.count_strict_mono (p := Nat.Prime) hq hcon
        rw [Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime] at h1
        have h2 : k ≤ Nat.count Nat.Prime q := by
          rw [hk]
          exact Nat.count_monotone (p := Nat.Prime) hqlo
        omega
      have hgt2 : ⌊x - 2⌋₊ < Nat.nth Nat.Prime k := by
        by_contra hcon
        push_neg at hcon
        have h1 : Nat.count Nat.Prime (Nat.nth Nat.Prime k) < k :=
          Nat.count_strict_mono (p := Nat.Prime) (Nat.prime_nth_prime k) (Nat.lt_succ_of_le hcon)
        rw [Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime] at h1
        exact absurd h1 (lt_irrefl k)
      obtain ⟨t, ht⟩ := hq.odd_of_ne_two (by omega : q ≠ 2)
      obtain ⟨u, hu⟩ := (Nat.prime_nth_prime k).odd_of_ne_two (by omega :
        Nat.nth Nat.Prime k ≠ 2)
      have hqcase : q = ⌊x - 2⌋₊ + 1 ∨ q = ⌊x - 2⌋₊ + 2 := by omega
      have hncase : Nat.nth Nat.Prime k = ⌊x - 2⌋₊ + 1 ∨
          Nat.nth Nat.Prime k = ⌊x - 2⌋₊ + 2 := by omega
      rcases hqcase with hc | hc <;> rcases hncase with hc' | hc' <;> omega
  have htheta : Chebyshev.theta x ≤ Chebyshev.theta (Nat.nth Nat.Prime k) := by
    rw [Chebyshev.theta_eq_log_primorial, Chebyshev.theta_eq_log_primorial,
      Nat.floor_natCast]
    apply Real.log_le_log (by exact_mod_cast primorial_pos ⌊x⌋₊)
    rw [primorial_eq_prod_primesLE, primorial_eq_prod_primesLE]
    push_cast
    refine Finset.prod_le_prod_of_subset_of_one_le ?_ ?_ ?_
    · intro p hp
      rw [Nat.mem_primesLE] at hp ⊢
      exact ⟨hkey p hp.2 hp.1, hp.2⟩
    · intro p _
      exact Nat.cast_nonneg p
    · intro p hp _
      exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le
  have h' : (n : ℝ) < Real.exp (Chebyshev.theta (Nat.nth Nat.Prime k)) :=
    lt_of_lt_of_le h (Real.exp_le_exp.mpr htheta)
  have hmain := rosser_schoenfeld_totient_lemma14 n k hn hk1 h'
  have hid : Nat.primesLE ⌊x - 2⌋₊ = (Finset.range k).image (Nat.nth Nat.Prime) := by
    rw [hk]
    exact primesLE_eq_image_count ⌊x - 2⌋₊
  calc (n : ℝ) / Nat.totient n
      ≤ ∏ i ∈ Finset.range k,
          (Nat.nth Nat.Prime i : ℝ) / ((Nat.nth Nat.Prime i : ℝ) - 1) := hmain
    _ = ∏ p ∈ Nat.primesLE ⌊x - 2⌋₊, (p : ℝ) / ((p : ℝ) - 1) := by
        rw [hid, Finset.prod_image
          (fun a _ b _ hab => Nat.nth_injective Nat.infinite_setOfPred_prime hab)]

end TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution (x : ℝ) (n : ℕ) (hx : 5 ≤ x) (hn : 1 ≤ n)
    (h : (n : ℝ) < Real.exp (Chebyshev.theta x)) :
    (n : ℝ) / Nat.totient n ≤
      ∏ p ∈ Nat.primesLE ⌊x - 2⌋₊, (p : ℝ) / ((p : ℝ) - 1) :=
  TaoFivePrimes.solution x n hx hn h

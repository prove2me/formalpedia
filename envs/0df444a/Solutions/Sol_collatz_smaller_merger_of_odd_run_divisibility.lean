-- Prove2me | solution 1 for collatz_smaller_merger_of_odd_run_divisibility
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T07:29:49.446792+00:00
-- url     : https://prove2.me/submissions/66072e01-bf8b-4552-8672-8d0e767cfa57

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring

private theorem halveBlock (a y : ℕ) : collatzStep^[a] (2 ^ a * y) = y := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Function.iterate_succ_apply, pow_succ']
    simpa [Nat.mul_assoc, collatzStep] using ih

private theorem oddPair (x : ℕ) (hx : 0 < x) :
    collatzStep^[2] (2 * x - 1) = 3 * x - 1 := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : x ≠ 0)
  have hs : 2 * (u + 1) - 1 = 2 * u + 1 := by omega
  have hd : 3 * (2 * u + 1) + 1 = 2 * (3 * u + 2) := by omega
  change collatzStep (collatzStep (2 * (u + 1) - 1)) = _
  rw [hs]
  simp [collatzStep, hd]
  omega

private theorem oddBlock (m q : ℕ) (hq : 0 < q) :
    collatzStep^[2 * m] (2 ^ m * q - 1) = 3 ^ m * q - 1 := by
  induction m generalizing q with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Function.iterate_add_apply, pow_succ' (2 : ℕ), Nat.mul_assoc,
      oddPair _ (Nat.mul_pos (Nat.two_pow_pos m) hq)]
    rw [show 3 * (2 ^ m * q) = 2 ^ m * (3 * q) by ring, ih _ (by omega), pow_succ]
    ring_nf

theorem solution (n a m : ℕ) (hodd : n % 2 = 1)
    (hgain : 3 * 2 ^ (a + m) ≤ 3 ^ m)
    (hdiv : 3 ^ m ∣ 2 ^ a * (3 * n + 1) + 1) :
    ∃ k : ℕ, 0 < k ∧ k < n ∧ collatzStep^[2 * m + a] k = collatzStep n := by
  obtain ⟨q, hq⟩ := hdiv
  have hqpos : 0 < q := by
    by_contra! hz
    simp [Nat.eq_zero_of_le_zero hz] at hq
  have hapos := Nat.two_pow_pos a
  have hm : 0 < m := by
    by_contra! hz
    simp [Nat.eq_zero_of_le_zero hz] at hgain
    omega
  have ht : 1 < (2 : ℕ) ^ m := Nat.one_lt_pow (by omega) (by decide)
  have hkpos : 1 < 2 ^ m * q :=
    lt_of_lt_of_le ht (Nat.le_mul_of_pos_right _ hqpos)
  have hbound : (3 * 2 ^ a) * (2 ^ m * q) < (3 * 2 ^ a) * (n + 1) := by
    calc
      (3 * 2 ^ a) * (2 ^ m * q) = (3 * 2 ^ (a + m)) * q := by rw [pow_add]; ring
      _ ≤ 3 ^ m * q := Nat.mul_le_mul_right q hgain
      _ = 2 ^ a * (3 * n + 1) + 1 := hq.symm
      _ < (3 * 2 ^ a) * (n + 1) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_add, Nat.mul_one]
        have : 2 ^ a * (3 * n) = (3 * 2 ^ a) * n := by ring
        omega
  have hsmall := Nat.lt_of_mul_lt_mul_left hbound
  refine ⟨2 ^ m * q - 1, by omega, by omega, ?_⟩
  rw [Nat.add_comm, Function.iterate_add_apply, oddBlock _ _ hqpos, ← hq, Nat.add_sub_cancel,
    halveBlock, collatzStep, if_neg (Nat.not_even_iff.mpr hodd)]

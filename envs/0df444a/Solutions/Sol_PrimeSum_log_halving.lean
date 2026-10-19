-- Prove2me | solution 1 for PrimeSum.log_halving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-18T13:51:14.547298+00:00
-- url     : https://prove2.me/submissions/e68bb4a5-5501-4463-a26b-d196598b867f

import Mathlib.Data.Nat.Log
import Mathlib.Tactic

private lemma log_half {m n : ℕ} (hn : 2 ≤ n) (h : m ≤ n / 2) :
    Nat.log 2 m + 1 ≤ Nat.log 2 n := by
  have h1 : Nat.log 2 m ≤ Nat.log 2 (n / 2) := Nat.log_mono_right h
  have h2 : Nat.log 2 (n / 2) = Nat.log 2 n - 1 := Nat.log_div_base 2 n
  have h3 : 1 ≤ Nat.log 2 n := Nat.log_pos (by norm_num) hn
  omega

theorem solution (n p : ℕ) (hn : 2 ≤ n) (hp : n < 2 * p) (hpn : p ≤ n) :
    Nat.log 2 (n - p) + 1 ≤ Nat.log 2 n := by
  refine log_half hn ?_
  omega

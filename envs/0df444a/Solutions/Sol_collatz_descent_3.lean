-- Prove2me | solution 3 for collatz_descent
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Siyuan Chen
-- created : 2026-11-23T14:28:49.883961+00:00
-- url     : https://prove2.me/submissions/5cc2dbab-5b16-4d0b-bea3-98de57795a9b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_collatz_iterate_pos
import Theorems.Thm_collatz_descent_even
import Theorems.Thm_collatz_descent_one_mod_four
import Theorems.Thm_collatz_descent_three_mod_sixteen
import Theorems.Thm_collatz_descent_eleven_mod_thirtytwo
import Theorems.Thm_collatz_descent_twentythree_mod_thirtytwo
import Theorems.Thm_collatz_descent_of_syracuse_descent
import Theorems.Thm_syracuse_descends_below_2310000
import Theorems.Thm_collatz_coalescence_residual_seven_mod_thirtytwo
import Theorems.Thm_collatz_coalescence_residual_twentyseven_mod_thirtytwo
import Theorems.Thm_collatz_coalescence_residual_fifteen_mod_sixteen

private theorem odd_step (n : ℕ) (hn : n % 2 = 1) :
    collatzStep n = 3 * n + 1 := by
  rw [collatzStep, if_neg]
  intro he
  obtain ⟨k, hk⟩ := he
  omega

private theorem even_step (n : ℕ) (hn : n % 2 = 0) :
    collatzStep n = n / 2 := by
  rw [collatzStep, if_pos]
  exact ⟨n / 2, by omega⟩

private theorem two_steps_from_odd (q : ℕ) :
    collatzStep^[2] (2 * q + 1) = 3 * q + 2 := by
  change collatzStep (collatzStep (2 * q + 1)) = _
  rw [odd_step (2 * q + 1) (by omega),
    even_step (3 * (2 * q + 1) + 1) (by omega)]
  omega

private theorem five_steps_to_four_mod_nine (q : ℕ) :
    collatzStep^[5] (8 * q + 3) = 9 * q + 4 := by
  have hfirst : collatzStep^[2] (8 * q + 3) = 12 * q + 5 := by
    simpa only [show 2 * (4 * q + 1) + 1 = 8 * q + 3 by omega,
      show 3 * (4 * q + 1) + 2 = 12 * q + 5 by omega] using
      two_steps_from_odd (4 * q + 1)
  have hnext : collatzStep^[2] (12 * q + 5) = 18 * q + 8 := by
    simpa only [show 2 * (6 * q + 2) + 1 = 12 * q + 5 by omega,
      show 3 * (6 * q + 2) + 2 = 18 * q + 8 by omega] using
      two_steps_from_odd (6 * q + 2)
  calc
    collatzStep^[5] (8 * q + 3) =
        collatzStep^[1] (collatzStep^[2] (collatzStep^[2] (8 * q + 3))) := by
      rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
    _ = 9 * q + 4 := by
      rw [hfirst, hnext, Function.iterate_one, even_step _ (by omega)]
      omega

private theorem smaller_predecessor (n : ℕ)
    (h : n % 3 = 2 ∨ n % 9 = 4) :
    ∃ k b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[b] k = n := by
  rcases h with h | h
  · refine ⟨2 * (n / 3) + 1, 2, by omega, by omega, ?_⟩
    rw [two_steps_from_odd]
    omega
  · refine ⟨8 * (n / 9) + 3, 5, by omega, by omega, ?_⟩
    rw [five_steps_to_four_mod_nine]
    omega

private theorem join_of_descent (n : ℕ) (hn : 0 < n)
    (h : ∃ t : ℕ, collatzStep^[t] n < n) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  obtain ⟨t, ht⟩ := h
  exact ⟨collatzStep^[t] n, t, 0, collatz_iterate_pos t n hn, ht, rfl⟩

private theorem one_after_multiple_of_three (j : ℕ) :
    collatzStep^[3 * j] 1 = 1 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 3 * (j + 1) = 3 * j + 3 by omega, Function.iterate_add_apply]
    have hcycle : collatzStep^[3] 1 = 1 := by decide
    rw [hcycle, ih]

private theorem reaches_one_of_join (n k a b : ℕ)
    (hjoin : collatzStep^[a] n = collatzStep^[b] k)
    (h : ∃ t : ℕ, collatzStep^[t] k = 1) :
    ∃ t : ℕ, collatzStep^[t] n = 1 := by
  obtain ⟨t, ht⟩ := h
  -- Extend the smaller orbit's visit to 1 past the common point at index b.
  let remaining := 3 * b + t - b
  have hindex : remaining + b = 3 * b + t := by
    dsimp [remaining]
    omega
  refine ⟨remaining + a, ?_⟩
  rw [Function.iterate_add_apply, hjoin, ← Function.iterate_add_apply, hindex,
    Function.iterate_add_apply, ht, one_after_multiple_of_three]

private theorem joins_smaller (n : ℕ) (hn : 1 < n) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  by_cases hpredecessor : n % 3 = 2 ∨ n % 9 = 4
  · obtain ⟨k, b, hk, hkn, h⟩ := smaller_predecessor n hpredecessor
    exact ⟨k, 0, b, hk, hkn, h.symm⟩
  have hmod9 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7 := by
    omega
  have hpos : 0 < n := by omega
  by_cases heven : Even n
  · exact join_of_descent n hpos ⟨1, by simpa using collatz_descent_even n hpos heven⟩
  by_cases hsmall : n < 2310000
  · have hodd : Odd n := Nat.not_even_iff_odd.mp heven
    exact join_of_descent n hpos
      (collatz_descent_of_syracuse_descent n heven
        (syracuse_descends_below_2310000 n hn hsmall hodd))
  by_cases hone : n % 4 = 1
  · exact join_of_descent n hpos ⟨3, collatz_descent_one_mod_four n hn hone⟩
  by_cases hthree : n % 16 = 3
  · exact join_of_descent n hpos (collatz_descent_three_mod_sixteen n hthree)
  by_cases heleven : n % 32 = 11
  · exact join_of_descent n hpos (collatz_descent_eleven_mod_thirtytwo n heleven)
  by_cases htwentythree : n % 32 = 23
  · exact join_of_descent n hpos (collatz_descent_twentythree_mod_thirtytwo n htwentythree)
  by_cases hshort : ∃ t : ℕ, t ≤ 128 ∧ collatzStep^[t] n < n
  · obtain ⟨t, _, ht⟩ := hshort
    exact join_of_descent n hpos ⟨t, ht⟩
  have hprefix (t : ℕ) (ht : t ≤ 128) : n ≤ collatzStep^[t] n :=
    Nat.le_of_not_lt fun h => hshort ⟨t, ht, h⟩
  have hlarge : 2310000 ≤ n := Nat.le_of_not_lt hsmall
  by_cases hseven : n % 32 = 7
  · exact collatz_coalescence_residual_seven_mod_thirtytwo n hlarge hseven hmod9 hprefix
  by_cases htwentyseven : n % 32 = 27
  · exact collatz_coalescence_residual_twentyseven_mod_thirtytwo n hlarge htwentyseven
      hmod9 hprefix
  have hoddMod : n % 2 = 1 := by
    have hOdd := Nat.not_even_iff_odd.mp heven
    obtain ⟨j, hj⟩ := hOdd
    omega
  have hfifteen : n % 16 = 15 := by omega
  exact collatz_coalescence_residual_fifteen_mod_sixteen n hlarge hfifteen hmod9 hprefix

private theorem reaches_one (n : ℕ) (hn : 0 < n) :
    ∃ t : ℕ, collatzStep^[t] n = 1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hone : n = 1
    · subst n
      exact ⟨0, rfl⟩
    obtain ⟨k, a, b, hk, hkn, hjoin⟩ := joins_smaller n (by omega)
    exact reaches_one_of_join n k a b hjoin (ih k hkn hk)

theorem solution (n : ℕ) (hn : 1 < n) : ∃ m : ℕ, collatzStep^[m] n < n := by
  obtain ⟨m, hm⟩ := reaches_one n (by omega)
  exact ⟨m, by simpa only [hm] using hn⟩

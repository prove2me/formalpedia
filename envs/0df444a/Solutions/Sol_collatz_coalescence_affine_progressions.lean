-- Prove2me | solution 1 for collatz_coalescence_affine_progressions
-- status  : ACCEPTED   (prove)
-- author  : @Siyuan Chen
-- created : 2026-11-23T15:02:16.459155+00:00
-- url     : https://prove2.me/submissions/6eea3d5a-2987-4492-9b55-bd6472fb09b2

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate

-- Compute an affine iterate only while its parity is independent of the parameter.
private def affineIter : ℕ → ℕ → ℕ → Option (ℕ × ℕ)
  | 0, a, b => some (a, b)
  | steps + 1, a, b =>
    if a % 2 = 0 then
      if b % 2 = 0 then affineIter steps (a / 2) (b / 2)
      else affineIter steps (3 * a) (3 * b + 1)
    else none

private theorem affine_parity (a b q : ℕ) (ha : a % 2 = 0) :
    (a * q + b) % 2 = b % 2 := by
  rw [Nat.add_mod, Nat.mul_mod, ha]
  simp

private theorem affine_even_step (a b q : ℕ) (ha : a % 2 = 0) (hb : b % 2 = 0) :
    collatzStep (a * q + b) = (a / 2) * q + b / 2 := by
  have hparity := (affine_parity a b q ha).trans hb
  have heven : Even (a * q + b) := ⟨(a * q + b) / 2, by omega⟩
  have hfactors : a * q = 2 * ((a / 2) * q) := by
    calc
      a * q = (2 * (a / 2)) * q := congrArg (fun x => x * q) (by omega)
      _ = 2 * ((a / 2) * q) := Nat.mul_assoc ..
  rw [collatzStep, if_pos heven, hfactors]
  omega

private theorem affine_odd_step (a b q : ℕ) (ha : a % 2 = 0) (hb : b % 2 ≠ 0) :
    collatzStep (a * q + b) = (3 * a) * q + (3 * b + 1) := by
  have hodd : ¬ Even (a * q + b) := by
    rintro ⟨i, hi⟩
    exact hb ((affine_parity a b q ha).symm.trans (by omega))
  rw [collatzStep, if_neg hodd, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

private theorem affine_iter_sound (steps a b u v q : ℕ)
    (h : affineIter steps a b = some (u, v)) :
    collatzStep^[steps] (a * q + b) = u * q + v := by
  induction steps generalizing a b with
  | zero =>
    have heq : (a, b) = (u, v) := Option.some.inj h
    injection heq with hu hv
    subst u
    subst v
    rfl
  | succ steps ih =>
    by_cases ha : a % 2 = 0
    · by_cases hb : b % 2 = 0
      · rw [Function.iterate_succ_apply, affine_even_step _ _ _ ha hb]
        exact ih _ _ (by simpa only [affineIter, if_pos ha, if_pos hb] using h)
      · rw [Function.iterate_succ_apply, affine_odd_step _ _ _ ha hb]
        exact ih _ _ (by simpa only [affineIter, if_pos ha, if_neg hb] using h)
    · simp [affineIter, ha] at h

private theorem merge_of_certificate (n m r c d stepsN stepsK u v : ℕ)
    (hres : n % m = r) (hslope : c ≤ m) (hpos : 0 < d) (hoffset : d < r)
    (hstart : affineIter stepsN m r = some (u, v))
    (hsmaller : affineIter stepsK c d = some (u, v)) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  have hn : n = m * (n / m) + r := by
    simpa only [hres] using (Nat.div_add_mod n m).symm
  have hmul : c * (n / m) ≤ m * (n / m) := Nat.mul_le_mul_right (n / m) hslope
  refine ⟨c * (n / m) + d, stepsN, stepsK, by omega, by omega, ?_⟩
  calc
    collatzStep^[stepsN] n = collatzStep^[stepsN] (m * (n / m) + r) :=
      congrArg (collatzStep^[stepsN]) hn
    _ = u * (n / m) + v := affine_iter_sound _ _ _ _ _ _ hstart
    _ = collatzStep^[stepsK] (c * (n / m) + d) :=
      (affine_iter_sound _ _ _ _ _ _ hsmaller).symm

theorem solution (n : ℕ)
    (h : n % 81 = 10 ∨
      n % 4608 = 4071 ∨
      n % 9216 = 7783 ∨
      n % 9216 = 1563 ∨
      n % 2304 = 1743 ∨
      n % 2304 = 1599 ∨
      n % 4608 = 2847 ∨
      n % 4608 = 735 ∨
      n % 4608 = 991 ∨
      n % 4608 = 2527 ∨
      n % 4608 = 3039 ∨
      n % 4608 = 4575) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
  · exact merge_of_certificate n 81 10 64 7 0 10 81 10 h1
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact merge_of_certificate n 4608 4071 4374 3865 15 2 6561 5798 h2
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact merge_of_certificate n 9216 7783 7776 6567 17 9 19683 16625 h3
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact merge_of_certificate n 9216 1563 7776 1319 17 9 19683 3341 h4
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact merge_of_certificate n 2304 1743 1944 1471 10 2 2916 2207 h5
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact merge_of_certificate n 2304 1599 1728 1199 14 11 6561 4556 h6
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact merge_of_certificate n 4608 2847 4374 2703 15 2 6561 4055 h7
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact merge_of_certificate n 4608 735 3456 551 12 9 8748 1397 h8
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact merge_of_certificate n 4608 991 3456 743 12 9 8748 1883 h9
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact merge_of_certificate n 4608 2527 3456 1895 12 9 8748 4799 h10
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact merge_of_certificate n 4608 3039 3456 2279 12 9 8748 5771 h11
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact merge_of_certificate n 4608 4575 3456 3431 12 9 8748 8687 h12
      (by decide) (by decide) (by decide) (by decide) (by decide)

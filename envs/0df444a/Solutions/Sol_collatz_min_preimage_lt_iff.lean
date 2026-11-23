-- Prove2me | solution 1 for collatz_min_preimage_lt_iff
-- status  : ACCEPTED   (prove)
-- author  : @Siyuan Chen
-- created : 2026-11-23T15:13:14.984919+00:00
-- url     : https://prove2.me/submissions/68aa8402-d72b-4f28-b5ed-695094721851

import Definitions.Def_collatzStepMap
import Definitions.Def_collatzMinPreimage
import Mathlib.Logic.Function.Iterate

private theorem step_preimages (k y : ℕ) :
    collatzStep k = y ↔ k = 2 * y ∨ (y % 6 = 4 ∧ k = y / 3) := by
  by_cases he : Even k
  · obtain ⟨q, hq⟩ := he
    have hk : k % 2 = 0 := by omega
    rw [collatzStep, if_pos ⟨q, hq⟩]
    omega
  · have hk : k % 2 = 1 := by
      by_contra hn
      exact he ⟨k / 2, by omega⟩
    rw [collatzStep, if_neg he]
    omega

private theorem nat_min_lt (a b n : ℕ) : min a b < n ↔ a < n ∨ b < n := by
  rw [Nat.min_def]
  split <;> omega

private theorem preimage_min_succ (d y n : ℕ) :
    collatzMinPreimage (d + 1) y < n ↔
      y < n ∨ collatzMinPreimage d (2 * y) < n ∨
        (y % 6 = 4 ∧ collatzMinPreimage d (y / 3) < n) := by
  by_cases h : y % 6 = 4
  · simp [collatzMinPreimage, h, nat_min_lt]
  · simp only [collatzMinPreimage, nat_min_lt, h, if_false, false_and, or_false]
    omega

private theorem append_step {d k b z y n : ℕ}
    (h : 0 < k ∧ k < n ∧ b ≤ d ∧ collatzStep^[b] k = z)
    (hstep : collatzStep z = y) :
    ∃ k b : ℕ, 0 < k ∧ k < n ∧ b ≤ d + 1 ∧ collatzStep^[b] k = y := by
  obtain ⟨hk, hkn, hb, hz⟩ := h
  refine ⟨k, b + 1, hk, hkn, by omega, ?_⟩
  rw [Function.iterate_succ_apply', hz, hstep]

theorem solution (depth y n : ℕ) (hy : 0 < y) :
    collatzMinPreimage depth y < n ↔
      ∃ k b : ℕ, 0 < k ∧ k < n ∧ b ≤ depth ∧ collatzStep^[b] k = y := by
  induction depth generalizing y with
  | zero =>
    constructor
    · intro h
      exact ⟨y, 0, hy, h, Nat.le_refl _, rfl⟩
    · rintro ⟨k, b, _, hkn, hb, hky⟩
      have hbz : b = 0 := by omega
      subst b
      change k = y at hky
      simpa only [collatzMinPreimage, ← hky] using hkn
  | succ d ih =>
    rw [preimage_min_succ]
    constructor
    · rintro (hzero | heven | ⟨hres, hodd⟩)
      · exact ⟨y, 0, hy, hzero, Nat.zero_le _, rfl⟩
      · obtain ⟨k, b, hk⟩ := (ih (2 * y) (by omega)).mp heven
        exact append_step hk ((step_preimages _ _).mpr (Or.inl rfl))
      · obtain ⟨k, b, hk⟩ := (ih (y / 3) (by omega)).mp hodd
        exact append_step hk ((step_preimages _ _).mpr (Or.inr ⟨hres, rfl⟩))
    · rintro ⟨k, b, hpos, hkn, hb, hky⟩
      cases b with
      | zero =>
        change k = y at hky
        exact Or.inl (hky ▸ hkn)
      | succ b =>
        rw [Function.iterate_succ_apply'] at hky
        rcases (step_preimages _ _).mp hky with hz | ⟨hres, hz⟩
        · exact Or.inr (Or.inl ((ih (2 * y) (by omega)).mpr
            ⟨k, b, hpos, hkn, by omega, hz⟩))
        · exact Or.inr (Or.inr ⟨hres, (ih (y / 3) (by omega)).mpr
            ⟨k, b, hpos, hkn, by omega, hz⟩⟩)

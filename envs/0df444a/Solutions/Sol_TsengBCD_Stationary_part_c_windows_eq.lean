-- Prove2me | solution 1 for TsengBCD.Stationary.part_c_windows_eq
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:53:57.197997+00:00
-- url     : https://prove2.me/submissions/25412240-4135-4392-be51-fb2199343f90

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting

set_option autoImplicit false
open Filter Topology TsengBCD.Stationary

theorem X_upd_eq {N : ℕ} {n : Fin N → ℕ} (y : X n) (k : Fin N)
    (c : EuclideanSpace ℝ (Fin (n k))) :
    Function.update y k c = y + Pi.single k (c - y k) := by
  funext i
  by_cases hik : i = k
  · subst hik
    simp
  · simp [Function.update_of_ne hik, Pi.single_eq_of_ne hik]

theorem solution {N : ℕ} {n : Fin N → ℕ} (f : X n → EReal) (T : ℕ)
    (zs : ℕ → X n) (ss : ℕ → Fin N)
    (huniq : ∀ j, 2 ≤ j → j ≤ T - 1 → AtMostOneMinIn f (ss j))
    (hfin : ∀ j, 1 ≤ j → j ≤ T → f (zs j) ≠ ⊤)
    (h7 : ∀ j, 1 ≤ j → j ≤ T → ∀ d : EuclideanSpace ℝ (Fin (n (ss j))),
      f (zs j) ≤ f (zs j + Pi.single (ss j) d))
    (h7' : ∀ j, 2 ≤ j → j ≤ T → ∀ k : Fin N, k ≠ ss j → zs j k = zs (j - 1) k)
    (h8 : ∀ j, 2 ≤ j → j ≤ T → ∀ d : EuclideanSpace ℝ (Fin (n (ss j))),
      f (zs (j - 1)) ≤ f (zs (j - 1) + Pi.single (ss j) d)) :
    ∀ j, 2 ≤ j → j ≤ T - 1 → zs (j - 1) = zs j := by
  intro j hj2 hjT
  have hjT' : j ≤ T := by omega
  have hagree : ∀ i, i ≠ ss j → zs j i = zs (j - 1) i := fun i hi => h7' j hj2 hjT' i hi
  have hj1 : zs j = Function.update (zs (j - 1)) (ss j) (zs j (ss j)) := by
    funext i
    by_cases hi : i = ss j
    · subst hi; simp
    · rw [Function.update_of_ne hi]; exact hagree i hi
  have hj1' : zs (j - 1) = Function.update (zs j) (ss j) (zs (j - 1) (ss j)) := by
    funext i
    by_cases hi : i = ss j
    · subst hi; simp
    · rw [Function.update_of_ne hi]; exact (hagree i hi).symm
  have hfin' : f (zs (j - 1)) ≠ ⊤ := hfin (j - 1) (by omega) (by omega)
  have key := huniq j hj2 hjT (zs j) (zs (j - 1) (ss j)) (zs j (ss j))
    (by rw [← hj1']; exact hfin')
    (by
      rw [← hj1']
      intro c
      have h := h8 j hj2 hjT' (c - zs (j - 1) (ss j))
      rw [← X_upd_eq] at h
      rw [hj1, Function.update_idem]
      exact h)
    (by
      rw [Function.update_eq_self]
      intro c
      have h := h7 j (by omega) hjT' (c - zs j (ss j))
      rwa [← X_upd_eq] at h)
  rw [hj1, ← key]
  simp

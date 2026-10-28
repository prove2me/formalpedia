-- Prove2me | solution 1 for WilliamsonShmoys.finite_piecewise_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:01:44.186925+00:00
-- url     : https://prove2.me/submissions/ea78cd86-3e20-4921-aefc-5353431f5b29

import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_piecewise_sum_bound_small
import Theorems.Thm_WilliamsonShmoys_finite_piecewise_sum_bound_large_aggregate

set_option autoImplicit false

theorem solution {α : Type} [Fintype α] (s : Finset α) (size : α → Nat) (f : α → Nat) (n : Nat) (hSum : s.sum size = n) (hPiece : ∀ x ∈ s, f x ≤ (if size x < 3 then size x / 2 else 3 * size x - 6)) (hn : 3 ≤ n) : s.sum f ≤ 3 * n - 6 := by
  by_cases hSmall : ∀ x ∈ s, size x < 3
  · have hPointwise : ∀ x ∈ s, f x ≤ size x := by
      intro x hx
      have hp := hPiece x hx
      rw [if_pos (hSmall x hx)] at hp
      omega
    exact WilliamsonShmoys.finite_piecewise_sum_bound_small s size f n hPointwise hSum hn
  · push_neg at hSmall
    obtain ⟨x, hx, hxLarge⟩ := hSmall
    have hAll : ∀ y ∈ s, f y ≤ 3 * size y := by
      intro y hy
      have hp := hPiece y hy
      by_cases hlt : size y < 3
      · rw [if_pos hlt] at hp
        omega
      · rw [if_neg hlt] at hp
        omega
    have hMargin : f x + 6 ≤ 3 * size x := by
      have hp := hPiece x hx
      rw [if_neg (by omega : ¬ size x < 3)] at hp
      omega
    have hAgg := WilliamsonShmoys.finite_piecewise_sum_bound_large_aggregate
      (s := s) (a := size) (b := f) (x := x) hx hAll hMargin
    rw [hSum] at hAgg
    omega
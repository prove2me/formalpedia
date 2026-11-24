-- Prove2me | solution 1 for UnaryQuadraticKKT.Hardness.chain_exact
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T15:19:31.473979+00:00
-- url     : https://prove2.me/submissions/3e5ee2fb-7f92-47e1-bdfa-458872b778a8

import Mathlib
import Definitions.Def_UnaryQuadraticKKT_Hardness_Chain

set_option autoImplicit false

open UnaryQuadraticKKT.Hardness

theorem solution (k : ℕ) (hk : 1 ≤ k) (s : ℤ) (hs : s = -1 ∨ s = 1)
    (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    chainValue k s x y (chainMinimizer k s x y) = chainMonomial k s x y := by
  have hs2 : (s : ℝ) ^ 2 = 1 := by
    rcases hs with rfl | rfl <;> norm_num
  -- the adjacent differences
  have hdiff : ∀ i : Fin (k + 1),
      2 * chainMinimizer k s x y ⟨i.val, by omega⟩ - chainMinimizer k s x y ⟨i.val + 1, by omega⟩
        = ((2 : ℝ) ^ (-(i.val : ℤ) - 1)) * x := by
    intro i
    simp only [chainMinimizer]
    have h1 : (2 : ℝ) ^ (-((i.val + 1 : ℕ) : ℤ)) = (2 : ℝ) ^ (-(i.val : ℤ) - 1) := by
      congr 1; push_cast; ring
    have h2 : (2 : ℝ) ^ (((i.val + 1 : ℕ) : ℤ) + 1 - ((k : ℤ) + 2))
        = 2 * (2 : ℝ) ^ ((i.val : ℤ) + 1 - ((k : ℤ) + 2)) := by
      rw [show (((i.val + 1 : ℕ) : ℤ) + 1 - ((k : ℤ) + 2)) = ((i.val : ℤ) + 1 - ((k : ℤ) + 2)) + 1 by
        push_cast; ring, zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    have h3 : (2 : ℝ) ^ (-(i.val : ℤ)) = 2 * (2 : ℝ) ^ (-(i.val : ℤ) - 1) := by
      rw [show (-(i.val : ℤ)) = (-(i.val : ℤ) - 1) + 1 by ring,
        zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
      ring_nf
    rw [h1, h2, h3]
    ring
  -- geometric sum
  have hgeom : ∀ n : ℕ, ∑ i : Fin n, ((2 : ℝ) ^ (-(i.val : ℤ) - 1)) ^ 2
      = (1 - ((2 : ℝ) ^ (-(n : ℤ))) ^ 2) / 3 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      have e1 : (2 : ℝ) ^ (-(n : ℤ)) = 2 * (2 : ℝ) ^ (-(n : ℤ) - 1) := by
        rw [show (-(n : ℤ)) = (-(n : ℤ) - 1) + 1 by ring,
          zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
        ring_nf
      have e2 : (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) = (2 : ℝ) ^ (-(n : ℤ) - 1) := by
        congr 1; push_cast; ring
      rw [e1, e2]
      ring
  have hsum : ∑ i : Fin (k + 1),
      (2 * chainMinimizer k s x y ⟨i.val, by omega⟩ - chainMinimizer k s x y ⟨i.val + 1, by omega⟩) ^ 2
        = x ^ 2 * ((1 - ((2 : ℝ) ^ (-((k + 1 : ℕ) : ℤ))) ^ 2) / 3) := by
    rw [← hgeom, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hdiff i]; ring
  -- endpoint values
  set t : ℝ := (2 : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) with ht
  have hu0 : chainMinimizer k s x y ⟨0, by omega⟩ = (x - s * t * y) / 3 := by
    simp only [chainMinimizer, ht, Nat.cast_zero, neg_zero, zpow_zero, one_mul]
    rw [show ((0 : ℤ) + 1 - ((k : ℤ) + 2)) = -((k + 1 : ℕ) : ℤ) by push_cast; ring]
  have huk : chainMinimizer k s x y ⟨k + 1, by omega⟩ = (t * x - s * y) / 3 := by
    simp only [chainMinimizer, ht]
    rw [show (((k + 1 : ℕ) : ℤ) + 1 - ((k : ℤ) + 2)) = 0 by push_cast; ring, zpow_zero]
    ring
  have hmono : chainMonomial k s x y = s * (2 * t) * x * y := by
    simp only [chainMonomial, ht]
    rw [show (-((k + 1 : ℕ) : ℤ)) = -(k : ℤ) - 1 by push_cast; ring]
    rw [show (2 : ℝ) ^ (-(k : ℤ)) = 2 * (2 : ℝ) ^ (-(k : ℤ) - 1) by
      rw [show (-(k : ℤ)) = (-(k : ℤ) - 1) + 1 by ring,
        zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]; ring_nf]
  simp only [chainValue]
  rw [hsum, hu0, huk, hmono]
  linear_combination (-(y ^ 2)) * hs2

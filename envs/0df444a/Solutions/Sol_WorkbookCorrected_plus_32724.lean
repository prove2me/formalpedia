-- Prove2me | solution 1 for WorkbookCorrected.plus_32724
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T14:51:23.542774+00:00
-- url     : https://prove2.me/submissions/6fb4fc76-927c-4205-b41b-971c66359b63

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem solution (a : ℕ → ℝ)
    (h1 : ∑ k ∈ Finset.Icc 1 100, a k = 67)
    (h2 : ∑ k ∈ Finset.Icc 1 100, (a k)^2 = 45)
    (hs : MonotoneOn a (Set.Icc 1 100)) : a 100 ≤ 1 := by
  have he : ∑ k ∈ Finset.Icc 1 100, (3*a k-2)^2 = (1:ℝ) := by
    calc
      ∑ k ∈ Finset.Icc 1 100, (3*a k-2)^2 =
          ∑ k ∈ Finset.Icc 1 100, (9*(a k)^2-12*a k+4) := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = 9*(∑ k ∈ Finset.Icc 1 100, (a k)^2)-12*(∑ k ∈ Finset.Icc 1 100, a k)+400 := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        norm_num
      _ = 1 := by rw [h1,h2]; norm_num
  have hb : (3*a 100-2)^2 ≤ ∑ k ∈ Finset.Icc 1 100, (3*a k-2)^2 :=
    Finset.single_le_sum (fun k hk => sq_nonneg (3*a k-2)) (show (100:ℕ) ∈ Finset.Icc 1 100 by norm_num)
  rw [he] at hb
  nlinarith [sq_nonneg (3*a 100-3)]
example : (∀ (a : ℕ → ℝ)
    (h1 : ∑ k ∈ Finset.Icc 1 100, a k = 67)
    (h2 : ∑ k ∈ Finset.Icc 1 100, (a k)^2 = 45)
    (hs : MonotoneOn a (Set.Icc 1 100)), a 100 ≤ 1) := @solution
#print axioms solution

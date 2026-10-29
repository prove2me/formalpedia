-- Prove2me | solution 1 for PochetWolsey.Reformulation.ls_inequality_valid
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T03:09:07.02918+00:00
-- url     : https://prove2.me/submissions/fd390a68-c80f-46d9-9957-36fdc3af81e5

import Mathlib

theorem solution : ¬ (∀ (n : ℕ) (hn : 0 < n) (d x y : Fin n → ℝ) (s : Fin (n + 1) → ℝ)
    (hd : ∀ t, 0 ≤ d t) (hs : ∀ k, 0 ≤ s k)
    (hstart : s 0 = 0) (hend : s (Fin.last n) = 0)
    (hy : ∀ t, y t = 0 ∨ y t = 1)
    (hbalance : ∀ t, s t.castSucc + x t = d t + s t.succ)
    (M : ℝ) (hM : 0 < M) (hlarge : (∑ t, d t) ≤ M)
    (hsetup : ∀ t, x t ≤ M * y t)
    (l : Fin n) (S : Finset (Fin n)) (hS : ∀ j ∈ S, j ≤ l),
    (∑ j ∈ S, x j) ≤
      (∑ j ∈ S, (∑ k ∈ Finset.Icc j l, d k) * y j) + s l.succ) := by
  intro h
  have := h 2 (by norm_num) (fun _ => 0) ![1, -1] (fun _ => 1) ![0, 1, 0]
    (fun _ => le_rfl) (by intro k; fin_cases k <;> norm_num) rfl rfl (fun _ => Or.inr rfl)
    (by intro t; fin_cases t <;> norm_num <;> simp) 1 one_pos (by simp)
    (by intro t; fin_cases t <;> norm_num) 1 {0} (by intro j hj; simp at hj; subst hj; decide)
  simp at this
  norm_num at this

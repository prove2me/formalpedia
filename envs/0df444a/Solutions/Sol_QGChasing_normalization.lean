-- Prove2me | solution 1 for QGChasing.normalization
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:37:03.977923+00:00
-- url     : https://prove2.me/submissions/7a13f674-441d-4679-a62e-f48884c9ff8f

import Mathlib
import Definitions.Def_QGChasing_chasingCost

open QGChasing in
theorem solution {d : ℕ} (C : ℝ) (hC : 1 ≤ C) (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : ∀ t, 1 ≤ t → ∀ z, 0 ≤ f t z) (v x u : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ)
    (h : ∑ t ∈ Finset.range T,
          ((f (t + 1) (x (t + 1)) - f (t + 1) (v (t + 1))) + ‖x (t + 1) - x t‖) ≤
        C * ∑ t ∈ Finset.range T,
          ((f (t + 1) (u (t + 1)) - f (t + 1) (v (t + 1))) + ‖u (t + 1) - u t‖)) :
    chasingCost f x T ≤ C * chasingCost f u T := by
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ t ∈ Finset.range T, f (t + 1) (v (t + 1)) := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by
    rw [hS]
    exact Finset.sum_nonneg (fun t _ => hf (t + 1) (by omega) _)
  have ex : ∑ t ∈ Finset.range T,
      ((f (t + 1) (x (t + 1)) - f (t + 1) (v (t + 1))) + ‖x (t + 1) - x t‖) =
      chasingCost f x T - S := by
    rw [hS]; unfold chasingCost
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    ring
  have eu : ∑ t ∈ Finset.range T,
      ((f (t + 1) (u (t + 1)) - f (t + 1) (v (t + 1))) + ‖u (t + 1) - u t‖) =
      chasingCost f u T - S := by
    rw [hS]; unfold chasingCost
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    ring
  rw [ex, eu] at h
  nlinarith

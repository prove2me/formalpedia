-- Prove2me | solution 1 for OnlineConvexOpt.OnlineBoosting.smoothed_regret_comparison
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:42:16.734083+00:00
-- url     : https://prove2.me/submissions/eecb2a44-30dd-40b4-92d4-1be1fea6381b

import Mathlib
import Definitions.Def_OnlineConvexOpt_OnlineBoosting_SmoothOn

namespace OnlineConvexOpt.OnlineBoosting

theorem aux_src_smooth_zero :
    SmoothOn Set.univ (fun _ : EuclideanSpace ℝ (Fin 1) => (0 : ℝ))
      (fun _ => (0 : EuclideanSpace ℝ (Fin 1))) 1 := by
  intro x _ y _
  simp only [inner_zero_left, add_zero, zero_add]
  positivity

end OnlineConvexOpt.OnlineBoosting

open OnlineConvexOpt.OnlineBoosting

theorem solution : ¬ (∀
    {n : ℕ} (D γ : ℝ) (hDpos : 0 < D) (hγpos : 0 < γ) (hγ1 : γ ≤ 1)
    (N T : ℕ) (hN : 0 < N) (hT : 0 < T)
    (fhat : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (β Ghat : ℝ) (hβpos : 0 < β) (hGhatpos : 0 < Ghat)
    (ghat : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hsmooth : ∀ t, SmoothOn Set.univ (fhat t) (ghat t) β)
    (hLip : ∀ t, ∀ x y, |fhat t x - fhat t y| ≤ Ghat * dist x y)
    (xN xstar : ℕ → EuclideanSpace ℝ (Fin n)) (RegretBoundW : ℝ),
    (∑ t ∈ Finset.Icc 1 T, fhat t (xN t)) - ∑ t ∈ Finset.Icc 1 T, fhat t (xstar t) ≤
      (2 * β * D ^ 2 * T) / (γ ^ 2 * N) + (Ghat * D / γ) * RegretBoundW) := by
  intro h
  have := @h 1 1 1 one_pos one_pos le_rfl 1 1 one_pos one_pos
    (fun _ _ => 0) 1 1 one_pos one_pos (fun _ _ => 0)
    (fun _ => aux_src_smooth_zero)
    (fun _ x y => by simp [dist_nonneg])
    (fun _ => 0) (fun _ => 0) (-10)
  norm_num at this

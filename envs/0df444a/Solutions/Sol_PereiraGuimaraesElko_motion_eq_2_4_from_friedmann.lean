-- Prove2me | solution 1 for PereiraGuimaraesElko.motion_eq_2_4_from_friedmann
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:16:42.524692+00:00
-- url     : https://prove2.me/submissions/722fcc04-f286-4735-8ae8-76648ec36893

import Mathlib

theorem solution : ¬ (∀ (κ : ℝ) (I : Set ℝ) (hI : IsOpen I) (H h Φ V : ℝ → ℝ)
    (hH : ∀ t ∈ I, DifferentiableAt ℝ H t) (hΦ : ∀ t ∈ I, DifferentiableAt ℝ Φ t)
    (hΦ' : ∀ t ∈ I, DifferentiableAt ℝ (deriv Φ) t) (hV : Differentiable ℝ V)
    (h25 : ∀ t ∈ I, h t = -(1 / 8) * (κ ^ 2 * Φ t ^ 2 / (1 + κ ^ 2 * Φ t ^ 2 / 8)) * H t)
    (h22 : ∀ t ∈ I, H t ^ 2 = κ ^ 2 / 3 * (deriv Φ t ^ 2 / 2 + V (Φ t)
        + 3 / 8 * H t ^ 2 * Φ t ^ 2 + 3 / 4 * H t * h t * Φ t ^ 2)
        + (1 + κ ^ 2 * Φ t ^ 2 / 8) * h t ^ 2)
    (h23 : ∀ t ∈ I, deriv H t = -(κ ^ 2 / 2) * (deriv Φ t ^ 2 + 3 / 4 * H t * h t * Φ t ^ 2
        - 1 / 4 * deriv (fun s => (H s + h s) * Φ s ^ 2) t)
        - 3 * (1 + κ ^ 2 * Φ t ^ 2 / 8) * h t ^ 2),
    ∀ t ∈ I, deriv Φ t ≠ 0 →
      deriv (deriv Φ) t + 3 * H t * deriv Φ t + deriv V (Φ t)
        - 3 / 4 * (H t + h t) ^ 2 * Φ t = 0) := by
  intro hall
  have hd : deriv (fun t : ℝ => t ^ 2) = fun t => 2 * t := by
    funext t; simp
  have h := hall 0 Set.univ isOpen_univ (fun _ => 0) (fun _ => 0) (fun t => t ^ 2) (fun _ => 0)
    (fun _ _ => differentiableAt_const _) (fun t _ => by fun_prop)
    (fun t _ => by rw [hd]; fun_prop) (differentiable_const _)
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp) 1 (Set.mem_univ _)
    (by rw [hd]; norm_num)
  rw [hd] at h
  have h2 : deriv (fun t : ℝ => 2 * t) 1 = 2 := by
    have := (hasDerivAt_id (1 : ℝ)).const_mul 2
    simpa using this.deriv
  rw [h2] at h
  norm_num at h

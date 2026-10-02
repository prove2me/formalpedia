-- Prove2me | solution 1 for ProcessingNetworks.LyapunovCriteria.max_derivative_at_active_index
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T23:40:27.304622+00:00
-- url     : https://prove2.me/submissions/c25679b7-f108-43b6-be68-34f202f12159

import Mathlib

theorem solution {d : ℕ} (f : Fin d → ℝ → ℝ) (t : ℝ) (ht : 0 < t) (i : Fin d)
    (hi : f i t = ⨆ j, f j t)
    (hfi : DifferentiableAt ℝ (f i) t) (hmax : DifferentiableAt ℝ (fun s => ⨆ j, f j s) t) :
    deriv (fun s => ⨆ j, f j s) t = deriv (f i) t := by
  have hle : ∀ s : ℝ, f i s ≤ ⨆ j, f j s := fun s =>
    le_ciSup (Finite.bddAbove_range (fun j => f j s)) i
  have hmin : IsLocalMin (fun s => (⨆ j, f j s) - f i s) t := by
    refine Filter.Eventually.of_forall ?_
    intro s
    show (⨆ j, f j t) - f i t ≤ (⨆ j, f j s) - f i s
    have h := hle s
    rw [← hi]
    linarith
  have hd : deriv (fun s => (⨆ j, f j s) - f i s) t = 0 := hmin.deriv_eq_zero
  have he : deriv (fun s => (⨆ j, f j s) - f i s) t
      = deriv (fun s => ⨆ j, f j s) t - deriv (f i) t := deriv_sub hmax hfi
  linarith

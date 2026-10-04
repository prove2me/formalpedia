-- Prove2me | solution 1 for ShorNonsmooth.SpaceDilation.gTilde_record_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T10:45:10.556431+00:00
-- url     : https://prove2.me/submissions/84059457-d233-4d25-a5fc-45010dc73f41
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod
import Theorems.Thm_ShorNonsmooth_SpaceDilation_sdg_record_bound_of_gTilde_ne_zero

open ShorNonsmooth.SpaceDilation

/-- Theorem 3.2 (Shor 1985, p. 55) by case split on vanishing transformed gradients.

If `gTilde r = 0` for some `r < k`, that index attains the bound since the right-hand
side `d * sqrt(k * (α^2 - 1)) / sqrt(α^(2k/n) - 1)` is nonnegative. Otherwise no
transformed gradient vanishes for `r < k`, and the eigenvalue-growth core is discharged
by the published child `sdg_record_bound_of_gTilde_ne_zero` (the book normalizes
`ξ_r = g̃_{r-1} / ‖g̃_{r-1}‖`, which needs exactly this nonvanishing). -/
theorem solution {n : ℕ} (hn : 0 < n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (d α : ℝ) (hd : 0 < d) (hα : 1 < α)
    (hg : ∀ k : ℕ,
      ‖g (sdg g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ _) k).x‖ ≤ d)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ r : ℕ, r < k ∧
      ‖gTilde g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ _) r‖ ≤
        d * Real.sqrt (k * (α ^ 2 - 1)) / Real.sqrt (α ^ ((2 * k : ℝ) / n) - 1) := by
  by_cases hzero : ∃ r : ℕ, r < k ∧
      gTilde g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ _) r = 0
  · obtain ⟨r, hrk, hr0⟩ := hzero
    refine ⟨r, hrk, ?_⟩
    rw [hr0, norm_zero]
    exact div_nonneg (mul_nonneg hd.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  · exact sdg_record_bound_of_gTilde_ne_zero hn g h x₀ d α hd hα hg k hk
      (fun r hr h => hzero ⟨r, hr, h⟩)

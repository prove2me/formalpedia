-- Prove2me | solution 1 for TwoAssumptions.prop5_unit_jacobian
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:25:19.113883+00:00
-- url     : https://prove2.me/submissions/fd57ca90-72cc-46ef-9856-3fa943d31184

import Mathlib
open scoped ContDiff
namespace TwoAssumptions

theorem _root_.solution {m : ℕ} (f : (Fin m → ℝ) → (Fin m → ℝ))
    (ρ : (Fin m → ℝ) → ℝ) (x : Fin m → ℝ)
    (hf : ContDiffAt ℝ 1 f x)
    (hρ : ρ x > 0)
    (hdensity : ρ x = ρ (f x) * |(fderiv ℝ f x).det|)
    (hscalar : ρ x = ρ (f x)) :
    |(fderiv ℝ f x).det| = 1 := by
  have h : ρ x * 1 = ρ x * |(fderiv ℝ f x).det| := by
    rw [mul_one]; nth_rewrite 1 [hdensity]; rw [← hscalar]
  exact (mul_left_cancel₀ hρ.ne' h).symm


end TwoAssumptions

-- Prove2me | solution 1 for QRH.dual_to_mean_square
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T13:09:40.496919+00:00
-- url     : https://prove2.me/submissions/86873d06-7127-4678-a984-12fb97d8721b

import Mathlib
import Definitions.Def_QRH_arith
import Definitions.Def_QRH_sums
import Definitions.Def_QRH_lfun
universe u

open QRH

theorem solution (W : QRHWorld.{u}) (S : QRHSums W)
    (c : W.E → ℂ) (Wt : ℝ → ℂ)
    (θ ε : ℝ) (hθ : 0 < θ) (hθ₁ : θ ≤ 1 / 10) (hε : 0 < ε)
    (hcan : ∃ k : ℝ, ∀ H X F : ℝ, 1 ≤ H → H ≤ X → X ≤ F →
      Eener W S c Wt H X F ≤ k * (X * F) ^ ε * X * F)
    (hpred : ∀ k : ℝ, (∀ H X F : ℝ, 1 ≤ H → H ≤ X → X ≤ F →
        Eener W S c Wt H X F ≤ k * (X * F) ^ ε * X * F) →
      ∀ D : ℝ, 2 ≤ D →
        msSum W S c Wt (D ^ (1 + θ)) D (2 * D) ≤ k * D ^ (2 + θ + ε)) :
    ∃ k : ℝ, ∀ D : ℝ, 2 ≤ D →
      msSum W S c Wt (D ^ (1 + θ)) D (2 * D) ≤ k * D ^ (2 + θ + ε) := by
  obtain ⟨k, hk⟩ := hcan
  exact ⟨k, hpred k hk⟩

-- Prove2me | solution 1 for UnfairML.Coverage.Supplement.theorem_5_false
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:23:15.452804+00:00
-- url     : https://prove2.me/submissions/ad196a0f-5fda-4a78-83dc-250c3059543c

import Mathlib
import Definitions.Def_UnfairML_Coverage_Supplement_GeneralCoverage

open UnfairML
open UnfairML.Coverage
open UnfairML.Coverage.Supplement

/-- Theorem 5, p. 28, is false as printed. Its claim — for every `θ ≥ 1`, `βp/αp ≥ r̂` implies
`φp(θ) ≤ φp(1)` — fails even under every standing assumption, the low-loss case, the special cost
`τ(s) = ks/(1 − γr s)` with `k` in the cost range of p. 23, `θ > 1`, and optimal efforts that are
global maxima of (13) both on the branch's feasible set and on the whole effort interval. -/
theorem solution :
    ¬ ∀ (P : Params) (k σ θ s₁ sθ : ℝ),
      P.Standing → P.LowLoss → CostRange P k σ → 1 < θ →
      IsOptGeneral P (tau P k) 1 s₁ →
      (∀ t ∈ Set.Icc (0 : ℝ) P.sMax, generalProfit P (tau P k) 1 t ≤ generalProfit P (tau P k) 1 s₁) →
      IsOptGeneral P (tau P k) θ sθ →
      (∀ t ∈ Set.Icc (0 : ℝ) P.sMax, generalProfit P (tau P k) θ t ≤ generalProfit P (tau P k) θ sθ) →
      rhat P θ s₁ sθ ≤ P.βp / P.αp →
      protCoverageGeneral P θ sθ ≤ protCoverageGeneral P 1 s₁ := by
        intro H
        let P : Params := { α := 1, β := 1, dp := 6/11, dr := 1/2, γp := 3/4, γr := 1 }
        let k : ℝ := 1/2 + (4/5)^2 * (7/22)
        have hmax : P.sMax = 1/2 := by norm_num [Params.sMax, P]
        have f1 : ∀ t : ℝ, t ≤ 1/2 → generalProfit P (tau P k) 1 t ≤ generalProfit P (tau P k) 1 (1/2) := by
          intro t ht
          have e1 : (1 - t) ≠ 0 := by intro h; linarith
          have e2 : (1 - 3/4 * t) ≠ 0 := by intro h; linarith
          have e2' : (4 - 3 * t) ≠ 0 := by intro h; linarith
          have e3 : (1 - 3/4 * t) = (4 - 3 * t) / 4 := by ring
          have key : generalProfit P (tau P k) 1 (1/2) - generalProfit P (tau P k) 1 t
              = 56/275 * (t - 1/2)^2 / ((1 - t) * (1 - 3/4 * t)) := by
            simp only [generalProfit, G1, tau, Params.αr, Params.αp, Params.βp, P, k, one_mul, e3]
            field_simp
            ring
          have : 0 ≤ 56/275 * (t - 1/2)^2 / ((1 - t) * (1 - 3/4 * t)) := by
            apply div_nonneg (by positivity)
            apply mul_nonneg <;> linarith
          linarith
        have f2 : ∀ t : ℝ, t ≤ 1/2 → generalProfit P (tau P k) (167/126) t ≤ generalProfit P (tau P k) (167/126) (16/37) := by
          intro t ht
          have e1 : (1 - t) ≠ 0 := by intro h; linarith
          have e2 : (1 - 3/4 * t) ≠ 0 := by intro h; linarith
          have e2' : (4 - 3 * t) ≠ 0 := by intro h; linarith
          have e3 : (1 - 3/4 * t) = (4 - 3 * t) / 4 := by ring
          have key : generalProfit P (tau P k) (167/126) (16/37) - generalProfit P (tau P k) (167/126) t
              = 2738/17325 * (t - 16/37)^2 / ((1 - t) * (1 - 3/4 * t)) := by
            simp only [generalProfit, G1, tau, Params.αr, Params.αp, Params.βp, P, k, one_mul, e3]
            field_simp
            ring
          have : 0 ≤ 2738/17325 * (t - 16/37)^2 / ((1 - t) * (1 - 3/4 * t)) := by
            apply div_nonneg (by positivity)
            apply mul_nonneg <;> linarith
          linarith
        have hfin := H P k (4/5) (167/126) (1/2) (16/37)
          (by norm_num [Params.Standing, Params.αr, Params.βr, P])
          (by norm_num [Params.LowLoss, Params.αr, Params.αp, Params.βp, P])
          (by norm_num [CostRange, Params.rho, Params.Acoef, Params.αr, Params.αp, Params.βp, P, k])
          (by norm_num)
          ⟨⟨by rw [hmax]; constructor <;> norm_num, by norm_num [P]⟩,
            fun t ht => f1 t (by have := ht.1.2; rwa [hmax] at this)⟩
          (fun t ht => f1 t (by have := ht.2; rwa [hmax] at this))
          ⟨⟨by rw [hmax]; constructor <;> norm_num, by norm_num [P]⟩,
            fun t ht => f2 t (by have := ht.1.2; rwa [hmax] at this)⟩
          (fun t ht => f2 t (by have := ht.2; rwa [hmax] at this))
          (by norm_num [rhat, Params.αp, Params.βp, P])
        norm_num [protCoverageGeneral, P] at hfin

-- Prove2me | solution 1 for OnlineNRM.TSFixed.full_demand_period_mean_replacement
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T14:47:12.635599+00:00
-- url     : https://prove2.me/submissions/fac3e62d-3a1c-44dc-95db-307887701a79
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OnlineNRM_TSFixed_full_demand_period_revenue_integrable
import Theorems.Thm_OnlineNRM_TSFixed_full_demand_period_mean_replacement_identity

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

theorem solution
    {N M K T : ℕ}
    (p : Fin N → Fin K → ℝ) (a : Fin N → Fin M → ℝ)
    (I : Fin M → ℝ) (dbar : Fin N → ℝ)
    (hp : ∀ i k, 0 ≤ p i k)
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (μ₀ : Measure Θ) [IsProbabilityMeasure μ₀]
    (F : Kernel (Θ × Fin K) (Fin N → ℝ)) [IsMarkovKernel F]
    (hF : ∀ ρ k, ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i))
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Θ) (θs : ℕ → Ω → Θ)
    (A : ℕ → Ω → Option (Fin K))
    (D Dsat : ℕ → Ω → Fin N → ℝ) (xsel : Θ → Fin K → ℝ)
    (hrun : IsTSFixedRun p a I F μ₀ T P θ θs A D Dsat xsel)
    (t : ℕ) (ht : t < T) :
    Integrable (fun ω => ∑ i : Fin N, D t ω i * postedPrice p (A t ω) i) P ∧
      (∫ ω, ∑ i : Fin N, D t ω i * postedPrice p (A t ω) i ∂P) =
        ∫ ω, (match A t ω with
          | none => 0
          | some k => ∑ i : Fin N, p i k * meanDemand F (θ ω) i k) ∂P := by
  exact ⟨
    full_demand_period_revenue_integrable
      (p := p) (a := a) (I := I) (dbar := dbar) (hp := hp)
      (μ₀ := μ₀) (F := F) (hF := hF) (P := P) (θ := θ) (θs := θs)
      (A := A) (D := D) (Dsat := Dsat) (xsel := xsel) (hrun := hrun)
      (t := t) (ht := ht),
    full_demand_period_mean_replacement_identity
      (p := p) (a := a) (I := I) (dbar := dbar) (hp := hp)
      (μ₀ := μ₀) (F := F) (hF := hF) (P := P) (θ := θ) (θs := θs)
      (A := A) (D := D) (Dsat := Dsat) (xsel := xsel) (hrun := hrun)
      (t := t) (ht := ht)⟩
-- Prove2me | solution 1 for OnlineNRM.TSFixed.full_demand_period_demand_ae
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T18:15:11.743685+00:00
-- url     : https://prove2.me/submissions/acfac0eb-0619-438a-9d52-a43b8c87d895
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run
import Theorems.Thm_OnlineNRM_TSFixed_full_demand_coordinate_ae

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
    ∀ᵐ ω ∂P, A t ω = none ∨ ∀ i, D t ω i ∈ Set.Icc 0 (dbar i) := by
  filter_upwards [ae_all_iff.mpr (fun i =>
    OnlineNRM.TSFixed.full_demand_coordinate_ae
      p a I dbar μ₀ F hF P θ θs A D Dsat xsel hrun t ht i)] with ω hω
  by_cases hnone : A t ω = none
  · exact Or.inl hnone
  · right
    intro i
    rcases hω i with h | hi
    · exact (hnone h).elim
    · exact hi
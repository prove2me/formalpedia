-- Prove2me | solution 1 for OnlineNRM.TSFixed.integrable_meanDemand_lpObj
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T14:54:57.014415+00:00
-- url     : https://prove2.me/submissions/60e79a4e-973c-495c-b466-568a48ac507a

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run
import Theorems.Thm_OnlineNRM_TSFixed_meanDemand_coordinate_bounds_measurable
import Theorems.Thm_OnlineNRM_TSFixed_integrable_lpObj_of_bounded_measurable

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

theorem solution
    {N K : ℕ}
    (p : Fin N → Fin K → ℝ) (dbar : Fin N → ℝ)
    (hp : ∀ i k, 0 ≤ p i k)
    {Θ : Type*} [MeasurableSpace Θ]
    (F : Kernel (Θ × Fin K) (Fin N → ℝ)) [IsMarkovKernel F]
    (hF : ∀ ρ k, ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i))
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Θ) (hθ : Measurable θ)
    (X : Ω → Fin K → ℝ) (hXmeas : Measurable X)
    (hX : ∀ᵐ ω ∂P, (∀ k, 0 ≤ X ω k) ∧ ∑ k : Fin K, X ω k ≤ 1) :
    Integrable (fun ω => lpObj p (meanDemand F (θ ω)) (X ω)) P := by
  refine OnlineNRM.TSFixed.integrable_lpObj_of_bounded_measurable
      p dbar P (fun ω => meanDemand F (θ ω)) ?_ ?_ X hXmeas hX
  · intro i k
    exact (OnlineNRM.TSFixed.meanDemand_coordinate_bounds_measurable F dbar hF i k).1.comp hθ
  · intro ω i k
    exact (OnlineNRM.TSFixed.meanDemand_coordinate_bounds_measurable F dbar hF i k).2 (θ ω)

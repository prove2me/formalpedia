-- Prove2me | solution 1 for StochasticProg.Bounds.thm1_jensen_partition_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-27T07:59:59.791992+00:00
-- url     : https://prove2.me/submissions/59e5de8e-09c2-4261-ba51-4f1110777ea5

import Mathlib
import Definitions.Def_StochasticProg_Bounds_Partition

open MeasureTheory
open StochasticProg.Bounds

theorem solution {Ω E α : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {Ξ : Set E} (hΞconv : Convex ℝ Ξ) (hΞclosed : IsClosed Ξ)
    {ξ : Ω → E} (hξrange : ∀ᵐ ω ∂μ, ξ ω ∈ Ξ) (hξint : Integrable ξ μ)
    {D : Set α} {x : α} (hx : x ∈ D) {g : α → E → ℝ}
    (hgconv : ConvexOn ℝ Ξ (g x)) (hgcont : ContinuousOn (g x) Ξ)
    (hgint : Integrable (fun ω => g x (ξ ω)) μ)
    {ν : ℕ} (P : Partition μ ν) :
    ∑ l, P.weight l * g x (P.condMean ξ l) ≤ ∫ ω, g x (ξ ω) ∂μ := by
  have hblock : ∀ l, P.weight l * g x (P.condMean ξ l) ≤ ∫ ω in P.S l, g x (ξ ω) ∂μ := by
    intro l
    have hfin : μ (P.S l) ≠ ⊤ := measure_ne_top μ _
    have hw : P.weight l = μ.real (P.S l) := rfl
    have hwpos : 0 < P.weight l := ENNReal.toReal_pos (P.pos l) hfin
    have hJ := hgconv.map_set_average_le hgcont hΞclosed (P.pos l) hfin
      (ae_restrict_of_ae hξrange) hξint.integrableOn hgint.integrableOn
    have hcm : P.condMean ξ l = ⨍ ω in P.S l, ξ ω ∂μ := by
      rw [setAverage_eq, ← hw]; rfl
    rw [hcm]
    calc P.weight l * g x (⨍ ω in P.S l, ξ ω ∂μ)
        ≤ P.weight l * ⨍ ω in P.S l, g x (ξ ω) ∂μ :=
          mul_le_mul_of_nonneg_left hJ hwpos.le
      _ = ∫ ω in P.S l, g x (ξ ω) ∂μ := by
          rw [setAverage_eq, smul_eq_mul, ← mul_assoc, ← hw, mul_inv_cancel₀ hwpos.ne', one_mul]
  calc ∑ l, P.weight l * g x (P.condMean ξ l)
      ≤ ∑ l, ∫ ω in P.S l, g x (ξ ω) ∂μ := Finset.sum_le_sum fun l _ => hblock l
    _ = ∫ ω in ⋃ l, P.S l, g x (ξ ω) ∂μ :=
        (integral_iUnion_fintype P.measurable P.disjoint fun l => hgint.integrableOn).symm
    _ = ∫ ω, g x (ξ ω) ∂μ := by rw [P.cover, setIntegral_univ]

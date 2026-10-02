-- Prove2me | solution 1 for PricingRM.DetHeuristic.heuristicRevenue_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T09:28:30.679891+00:00
-- url     : https://prove2.me/submissions/ce6dfc64-4c2d-413c-ad72-77694045e89b

import Mathlib
import Definitions.Def_PricingRM_DetHeuristic_PricingModel

set_option autoImplicit false

namespace PricingRM.DetHeuristic.P712c

open MeasureTheory ProbabilityTheory PricingRM.DetHeuristic
open scoped ENNReal

variable {N : ℕ} (M : PricingModel N) (pdet : Fin N → ℝ)

instance heurLaw_prob : IsProbabilityMeasure (heuristicLaw M pdet) := by
  unfold heuristicLaw; infer_instance

lemma integrable_coord (i : Fin N) :
    Integrable (fun x : Fin N → ℝ => x i) (heuristicLaw M pdet) := by
  unfold heuristicLaw
  exact integrable_comp_eval (μ := fun n => M.μ n (pdet n)) (i := i) (f := fun y : ℝ => y)
    (M.integrable i (pdet i))

lemma integral_coord (i : Fin N) :
    ∫ x, x i ∂(heuristicLaw M pdet) = meanDemand M i (pdet i) := by
  unfold heuristicLaw meanDemand
  exact integral_comp_eval (μ := fun n => M.μ n (pdet n)) (i := i) (f := fun y : ℝ => y)
    (by fun_prop)

lemma integrable_cum (n : Fin N) :
    Integrable (fun x : Fin N → ℝ => cumDemand x n) (heuristicLaw M pdet) := by
  unfold cumDemand
  exact integrable_finsetSum _ fun i _ => integrable_coord M pdet i

lemma cum_eq (x : Fin N → ℝ) (n : Fin N) :
    cumDemand x n = cumDemandBefore x n + x n := by
  unfold cumDemand cumDemandBefore
  have : Finset.univ.filter (fun i => i ≤ n) =
      insert n (Finset.univ.filter (fun i => i < n)) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    exact le_iff_eq_or_lt
  rw [this, Finset.sum_insert (by simp), add_comm]

lemma integrable_lost (C₀ : ℝ) (n : Fin N) :
    Integrable (fun x : Fin N → ℝ => max (x n - max (C₀ - cumDemandBefore x n) 0) 0)
      (heuristicLaw M pdet) := by
  refine Integrable.mono' (integrable_coord M pdet n).abs ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    refine Measurable.max ?_ measurable_const
    refine (measurable_pi_apply n).sub (Measurable.max (measurable_const.sub ?_) measurable_const)
    unfold cumDemandBefore
    exact Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (abs_nonneg _)
    have h1 := le_max_right (C₀ - cumDemandBefore x n) 0
    have h2 := le_abs_self (x n)
    linarith

end PricingRM.DetHeuristic.P712c

open MeasureTheory ProbabilityTheory PricingRM.DetHeuristic in
theorem solution {N : ℕ} (M : PricingModel N) (C₀ : ℝ) (pdet : Fin N → ℝ)
    (hp : ∀ n, 0 ≤ pdet n) (hmean : ∀ n, 0 < meanDemand M n (pdet n)) :
    heuristicRevenue M C₀ pdet =
        ∑ n, pdet n * meanDemand M n (pdet n) *
          (1 - (∫ x, max (x n - max (C₀ - cumDemandBefore x n) 0) 0 ∂(heuristicLaw M pdet)) /
            meanDemand M n (pdet n)) ∧
      ∑ n, pdet n * meanDemand M n (pdet n) *
          (1 - (∫ x, max (x n - max (C₀ - cumDemandBefore x n) 0) 0 ∂(heuristicLaw M pdet)) /
            meanDemand M n (pdet n)) ≥
        ∑ n, pdet n * meanDemand M n (pdet n) *
          (1 - (∫ x, max (cumDemand x n - C₀) 0 ∂(heuristicLaw M pdet)) /
            meanDemand M n (pdet n)) := by
  have hg_int : ∀ n, Integrable (fun x : Fin N → ℝ => max (cumDemand x n - C₀) 0)
      (heuristicLaw M pdet) :=
    fun n => ((P712c.integrable_cum M pdet n).sub (integrable_const C₀)).pos_part
  refine ⟨?_, ?_⟩
  · unfold heuristicRevenue
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_sub (P712c.integrable_coord M pdet n) (P712c.integrable_lost M pdet C₀ n),
      P712c.integral_coord]
    have hm := (hmean n).ne'
    field_simp
  · show _ ≤ _
    refine Finset.sum_le_sum fun n _ => ?_
    have hle : ∫ x, max (x n - max (C₀ - cumDemandBefore x n) 0) 0 ∂(heuristicLaw M pdet) ≤
        ∫ x, max (cumDemand x n - C₀) 0 ∂(heuristicLaw M pdet) := by
      refine integral_mono (P712c.integrable_lost M pdet C₀ n) (hg_int n) fun x => ?_
      refine max_le_max ?_ le_rfl
      have h1 := le_max_left (C₀ - cumDemandBefore x n) 0
      rw [P712c.cum_eq]
      linarith
    have hd := div_le_div_of_nonneg_right hle (hmean n).le
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hp n) (hmean n).le)
    linarith

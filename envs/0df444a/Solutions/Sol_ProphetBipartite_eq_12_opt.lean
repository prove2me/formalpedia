-- Prove2me | solution 1 for ProphetBipartite.eq_12_opt
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:30:56.763091+00:00
-- url     : https://prove2.me/submissions/67a2045b-6f06-4d2f-8e93-2c2e990bea8e

import Mathlib
import Definitions.Def_ProphetBipartite_optValue
import Definitions.Def_ProphetBipartite_IsOptSelector
import Definitions.Def_ProphetBipartite_Mmat

open MeasureTheory
open scoped NNReal ENNReal

namespace Aux_PB12

theorem integrable_coord {E : Type*} [Fintype E] (μ : E → Measure ℝ≥0)
    [∀ e, IsProbabilityMeasure (μ e)]
    (hμ : ∀ e, ∫⁻ x, (x : ℝ≥0∞) ∂(μ e) ≠ ⊤) (e : E) :
    Integrable (fun v : E → ℝ≥0 => (v e : ℝ)) (Measure.pi μ) := by
  have h1 : Integrable (fun x : ℝ≥0 => (x : ℝ)) (μ e) := by
    have := integrable_toReal_of_lintegral_ne_top (μ := μ e) (f := fun x : ℝ≥0 => (x : ℝ≥0∞))
      measurable_coe_nnreal_ennreal.aemeasurable (hμ e)
    simpa using this
  exact (measurePreserving_eval μ e).integrable_comp_of_integrable h1

theorem fiber {L R E : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (left : E → L) (right : E → R) (S : Finset E) (g : E → ℝ) :
    ∑ e ∈ S, g e = ∑ i, ∑ j, ∑ e ∈ S.filter (fun e => left e = i ∧ right e = j), g e := by
  rw [← Finset.sum_fiberwise S left g]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_fiberwise (S.filter (fun e => left e = i)) right g]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.filter_filter]

theorem meas_F {L R E : Type*} [Fintype E] [DecidableEq E] [DecidableEq L] [DecidableEq R]
    (left : E → L) (right : E → R) (opt : (E → ℝ≥0) → Finset E)
    (hmeas : ∀ S : Finset E, MeasurableSet {v : E → ℝ≥0 | opt v = S}) (i : L) (j : R) :
    Measurable (fun v : E → ℝ≥0 =>
      ∑ e ∈ (opt v).filter (fun e => left e = i ∧ right e = j), (v e : ℝ)) := by
  have h : (fun v : E → ℝ≥0 =>
        ∑ e ∈ (opt v).filter (fun e => left e = i ∧ right e = j), (v e : ℝ)) =
      fun v => ∑ S : Finset E, Set.indicator {v | opt v = S}
        (fun v : E → ℝ≥0 => ∑ e ∈ S.filter (fun e => left e = i ∧ right e = j), (v e : ℝ)) v := by
    funext v
    rw [Finset.sum_eq_single (opt v)]
    · simp [Set.indicator_apply]
    · intro S _ hS
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      rw [if_neg (Ne.symm hS)]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h]
  exact Finset.measurable_sum _ (fun S _ =>
    (Finset.measurable_sum _ (fun e _ => (measurable_pi_apply e).coe_nnreal_real)).indicator
      (hmeas S))

end Aux_PB12

open ProphetBipartite Aux_PB12 in
theorem solution {L R E : Type*} [Fintype L] [Fintype R] [Fintype E]
    [DecidableEq L] [DecidableEq R] [DecidableEq E]
    (left : E → L) (right : E → R) (μ : E → Measure ℝ≥0) [∀ e, IsProbabilityMeasure (μ e)]
    (hμ : ∀ e, ∫⁻ x, (x : ℝ≥0∞) ∂(μ e) ≠ ⊤)
    (opt : (E → ℝ≥0) → Finset E) (hopt : IsOptSelector left right opt) :
    ∫ v, (optValue left right v : ℝ) ∂(Measure.pi μ) = ∑ i, ∑ j, Mmat left right opt μ i j := by
  have hpt : ∀ v : E → ℝ≥0, (optValue left right v : ℝ) =
      ∑ i, ∑ j, ∑ e ∈ (opt v).filter (fun e => left e = i ∧ right e = j), (v e : ℝ) := by
    intro v
    rw [← (hopt.1 v).2, NNReal.coe_sum]
    exact fiber left right (opt v) (fun e => (v e : ℝ))
  have hint : ∀ i j, Integrable (fun v : E → ℝ≥0 =>
      ∑ e ∈ (opt v).filter (fun e => left e = i ∧ right e = j), (v e : ℝ)) (Measure.pi μ) := by
    intro i j
    refine Integrable.mono'
      (integrable_finsetSum (f := fun e (v : E → ℝ≥0) => (v e : ℝ)) Finset.univ
        (fun e _ => integrable_coord μ hμ e))
      (meas_F left right opt hopt.2 i j).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun v => ?_)
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun e _ => NNReal.coe_nonneg _))]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun e _ _ => NNReal.coe_nonneg _)
  rw [show (fun v : E → ℝ≥0 => (optValue left right v : ℝ)) = _ from funext hpt]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  rfl

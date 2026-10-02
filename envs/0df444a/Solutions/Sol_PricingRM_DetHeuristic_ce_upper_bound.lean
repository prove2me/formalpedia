-- Prove2me | solution 1 for PricingRM.DetHeuristic.ce_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T06:59:46.029146+00:00
-- url     : https://prove2.me/submissions/6336722f-98f2-4bb6-89a5-fbe2d611872a

import Mathlib
import Definitions.Def_PricingRM_DetHeuristic_PricingModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PricingRM.DetHeuristic

lemma f452_integrable_min (M : PricingModel 1) (C p : ℝ) :
    Integrable (fun x : ℝ => min x C) (M.μ 0 p) := by
  have h1 := M.integrable 0 p
  refine Integrable.mono' (h1.norm.add (integrable_const |C|)) ?_ ?_
  · exact (measurable_id.min measurable_const).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun x => ?_)
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rcases le_total x C with h | h
    · rw [min_eq_left h]; linarith [abs_nonneg C]
    · rw [min_eq_right h]; linarith [abs_nonneg x]

lemma f452_part1 (M : PricingModel 1) (C : ℝ) (p : ℝ) (hp : 0 ≤ p) :
    ∫ x, p * min x C ∂(M.μ 0 p) ≤ p * min (meanDemand M 0 p) C := by
  rw [integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ hp
  have hi := f452_integrable_min M C p
  apply le_min
  · unfold meanDemand
    exact integral_mono hi (M.integrable 0 p) (fun x => min_le_left x C)
  · calc ∫ x, min x C ∂(M.μ 0 p) ≤ ∫ _x, C ∂(M.μ 0 p) :=
          integral_mono hi (integrable_const C) (fun x => min_le_right x C)
      _ = C := by simp

lemma f452_part2 (M : PricingModel 1) (C : ℝ) (p : ℝ) (hp : 0 ≤ p) :
    ∫⁻ x, ENNReal.ofReal (p * min x C) ∂(M.μ 0 p) ≤
      ENNReal.ofReal (p * min (meanDemand M 0 p) C) := by
  rcases lt_or_ge C 0 with hC | hC
  · have : ∀ x, ENNReal.ofReal (p * min x C) = 0 := fun x => by
      apply ENNReal.ofReal_of_nonpos
      exact mul_nonpos_of_nonneg_of_nonpos hp (le_trans (min_le_right _ _) hC.le)
    simp [this]
  · have hint : Integrable (fun x : ℝ => p * min x C) (M.μ 0 p) :=
      (f452_integrable_min M C p).const_mul p
    have hnn : 0 ≤ᵐ[M.μ 0 p] fun x : ℝ => p * min x C := by
      filter_upwards [M.nonneg 0 p] with x hx
      exact mul_nonneg hp (le_min hx hC)
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    exact ENNReal.ofReal_le_ofReal (f452_part1 M C p hp)

end PricingRM.DetHeuristic

open PricingRM.DetHeuristic in
theorem solution (M : PricingModel 1) (C : ℝ) :
    (∀ p : ℝ, 0 ≤ p → ∫ x, p * min x C ∂(M.μ 0 p) ≤ p * min (meanDemand M 0 p) C) ∧
      optValue M C ≤ ceValue M 0 C := by
  refine ⟨fun p hp => f452_part1 M C p hp, ?_⟩
  simp only [optValue, valueToGo, ceValue, add_zero]
  apply iSup₂_mono
  intro p hp
  have hfin : (⟨1 - (0 + 1), by omega⟩ : Fin 1) = 0 := Subsingleton.elim _ _
  rw [hfin]
  exact f452_part2 M C p hp


-- Prove2me | solution 1 for SupportVectorMachines.Classification.theorem_2_31_instance_zhang
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:19:35.520324+00:00
-- url     : https://prove2.me/submissions/ed61982e-2bc8-4030-8562-df757de9fb94

import Mathlib
import Definitions.Def_SupportVectorMachines_Classification_RiskBasics
import Definitions.Def_SupportVectorMachines_Classification_ClassificationLosses

open MeasureTheory

namespace SupportVectorMachines.Classification

/-- The two-point distribution: `y = 4` with probability `1/4`, `y = -1` with probability `3/4`. -/
noncomputable def aux_zh_P : Measure (Unit × ℝ) :=
  ENNReal.ofReal (1 / 4) • Measure.dirac ((), (4 : ℝ)) +
    ENNReal.ofReal (3 / 4) • Measure.dirac ((), (-1 : ℝ))

theorem aux_zh_integrable (F : Unit × ℝ → ℝ) : Integrable F aux_zh_P := by
  unfold aux_zh_P
  refine Integrable.add_measure ?_ ?_
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem aux_zh_integral (F : Unit × ℝ → ℝ) :
    ∫ p, F p ∂aux_zh_P = 1 / 4 * F ((), 4) + 3 / 4 * F ((), -1) := by
  unfold aux_zh_P
  rw [integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_dirac]
  · rw [ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by norm_num)]
    simp [smul_eq_mul]
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

instance aux_zh_prob : IsProbabilityMeasure aux_zh_P := ⟨by
  simp only [aux_zh_P, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num⟩

theorem aux_zh_risk (L : Loss Unit) (g : Unit → ℝ) :
    risk L aux_zh_P g = 1 / 4 * L () 4 (g ()) + 3 / 4 * L () (-1) (g ()) := by
  unfold risk
  exact aux_zh_integral (fun p => L p.1 p.2 (g p.1))

theorem aux_zh_hinge_lb (t : ℝ) :
    15 / 16 ≤ 1 / 4 * hingeLoss (X := Unit) () 4 t + 3 / 4 * hingeLoss (X := Unit) () (-1) t := by
  simp only [hingeLoss]
  have h1 : (1 : ℝ) - 4 * t ≤ max 0 (1 - 4 * t) := le_max_right _ _
  have h2 : (0 : ℝ) ≤ max 0 (1 - 4 * t) := le_max_left _ _
  have h3 : (1 : ℝ) - (-1) * t ≤ max 0 (1 - (-1) * t) := le_max_right _ _
  rcases le_total t (1 / 4) with h | h <;> nlinarith

theorem aux_zh_bayes_hinge : 15 / 16 ≤ bayesRisk hingeLoss aux_zh_P := by
  unfold bayesRisk
  refine le_csInf ⟨_, fun _ => 0, measurable_const, rfl⟩ ?_
  rintro r ⟨g, _, rfl⟩
  rw [aux_zh_risk]
  exact aux_zh_hinge_lb (g ())

theorem aux_zh_bayes_class : bayesRisk classLoss aux_zh_P ≤ 1 / 4 := by
  unfold bayesRisk
  refine csInf_le_of_le (b := risk classLoss aux_zh_P (fun _ => -1)) ?_ ⟨_, measurable_const, rfl⟩ ?_
  · refine ⟨0, ?_⟩
    rintro r ⟨g, _, rfl⟩
    rw [aux_zh_risk]
    simp only [classLoss]
    split_ifs <;> norm_num
  · rw [aux_zh_risk]
    simp [classLoss, sgn]
    norm_num

end SupportVectorMachines.Classification

open MeasureTheory
open SupportVectorMachines.Classification

theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X] (P : Measure (X × ℝ))
    [IsProbabilityMeasure P] (f : X → ℝ) (hf : Measurable f)
    (hInt1 : Integrable (fun p : X × ℝ => hingeLoss p.1 p.2 (f p.1)) P)
    (hInt2 : Integrable (fun p : X × ℝ => classLoss p.1 p.2 (f p.1)) P),
    risk classLoss P f - bayesRisk classLoss P ≤
      risk hingeLoss P f - bayesRisk hingeLoss P) := by
  intro h
  have key := h (X := Unit) aux_zh_P (fun _ => 1 / 4) measurable_const
    (aux_zh_integrable _) (aux_zh_integrable _)
  have hc : risk classLoss aux_zh_P (fun _ => 1 / 4) = 3 / 4 := by
    rw [aux_zh_risk]; simp [classLoss, sgn]; norm_num
  have hh : risk hingeLoss aux_zh_P (fun _ => 1 / 4) = 15 / 16 := by
    rw [aux_zh_risk]; simp [hingeLoss]; norm_num
  rw [hc, hh] at key
  have := aux_zh_bayes_hinge
  have := aux_zh_bayes_class
  linarith

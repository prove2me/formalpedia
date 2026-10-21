-- Prove2me | solution 1 for RegevLWE.PeriodicGauss.first_display
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:55:36.961208+00:00
-- url     : https://prove2.me/submissions/7a094c5c-563e-47ac-81c9-c3c9dc3614b4

import Mathlib

set_option autoImplicit false
open MeasureTheory

theorem solution (ϵ : ℝ) (hϵ : 0 < ϵ) (hϵ1 : ϵ ≤ 1) :
    (∫⁻ x : ℝ, ENNReal.ofReal
        |Real.exp (-Real.pi * x ^ 2) - 1 / (1 + ϵ) * Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)|) ≤
      (∫⁻ x : ℝ, ENNReal.ofReal
        |Real.exp (-Real.pi * x ^ 2) - Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)|) +
      (∫⁻ x : ℝ, ENNReal.ofReal
        |(1 - 1 / (1 + ϵ)) * Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)|) ∧
    (∫⁻ x : ℝ, ENNReal.ofReal
        |(1 - 1 / (1 + ϵ)) * Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)|) = ENNReal.ofReal ϵ ∧
    (∫⁻ x : ℝ, ENNReal.ofReal
        |Real.exp (-Real.pi * x ^ 2) - Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)|) =
      ∫⁻ x : ℝ, ENNReal.ofReal
        (|Real.exp (-Real.pi * (1 - 1 / (1 + ϵ) ^ 2) * x ^ 2) - 1| *
          Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)) := by
  have hs : 0 < 1 + ϵ := by linarith
  have hpi := Real.pi_pos
  refine ⟨?_, ?_, ?_⟩
  · calc _ ≤ ∫⁻ x : ℝ, (ENNReal.ofReal
          |Real.exp (-Real.pi * x ^ 2) - Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)| +
          ENNReal.ofReal
          |(1 - 1 / (1 + ϵ)) * Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)|) := by
          refine lintegral_mono fun x => ?_
          rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          have : Real.exp (-Real.pi * x ^ 2) - 1 / (1 + ϵ) * Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)
              = (Real.exp (-Real.pi * x ^ 2) - Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)) +
                (1 - 1 / (1 + ϵ)) * Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2) := by ring
          rw [this]
          exact abs_add_le _ _
      _ = _ := by
          refine lintegral_add_left ?_ _
          fun_prop
  · have hnn : ∀ x : ℝ, 0 ≤ (1 - 1 / (1 + ϵ)) * Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2) := by
      intro x
      have : 0 ≤ 1 - 1 / (1 + ϵ) := by
        rw [sub_nonneg, div_le_one hs]; linarith
      positivity
    have hb : 0 < Real.pi / (1 + ϵ) ^ 2 := by positivity
    have hexp : ∀ x : ℝ, Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2) =
        Real.exp (-(Real.pi / (1 + ϵ) ^ 2) * x ^ 2) := fun x => by congr 1; ring
    have hint : Integrable (fun x : ℝ => (1 - 1 / (1 + ϵ)) *
        Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)) := by
      simp_rw [hexp]
      exact (integrable_exp_neg_mul_sq hb).const_mul _
    have hI : ∫ x : ℝ, (1 - 1 / (1 + ϵ)) * Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2) = ϵ := by
      simp_rw [hexp]
      rw [integral_const_mul, integral_gaussian]
      have : Real.pi / (Real.pi / (1 + ϵ) ^ 2) = (1 + ϵ) ^ 2 := by field_simp
      rw [this, Real.sqrt_sq hs.le]
      field_simp
      ring
    have := ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)
    rw [hI] at this
    rw [this]
    refine lintegral_congr fun x => ?_
    rw [abs_of_nonneg (hnn x)]
  · refine lintegral_congr fun x => ?_
    congr 1
    have e : Real.exp (-Real.pi * x ^ 2) = Real.exp (-Real.pi * (1 - 1 / (1 + ϵ) ^ 2) * x ^ 2) *
        Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (-Real.pi * x ^ 2) - Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2) =
        (Real.exp (-Real.pi * (1 - 1 / (1 + ϵ) ^ 2) * x ^ 2) - 1) *
          Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2) := by
      rw [e]; ring
    rw [h2, abs_mul, abs_of_pos (Real.exp_pos _)]

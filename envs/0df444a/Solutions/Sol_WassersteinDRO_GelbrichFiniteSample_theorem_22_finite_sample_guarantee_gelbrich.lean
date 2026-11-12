-- Prove2me | solution 1 for WassersteinDRO.GelbrichFiniteSample.theorem_22_finite_sample_guarantee_gelbrich
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T20:16:05.647385+00:00
-- url     : https://prove2.me/submissions/c862830a-d653-46fc-b741-0f1176971772

import Mathlib
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_risk
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_HasMeanCov
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_sampleMean
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_sampleCov
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_gelbrichRisk
import Theorems.Thm_WassersteinDRO_GelbrichFiniteSample_theorem_21_concentration_mean_cov
import Theorems.Thm_WassersteinDRO_GelbrichFiniteSample_true_risk_le_gelbrich_risk

open MeasureTheory

open WassersteinDRO.GelbrichFiniteSample in
theorem solution (m : ℕ) (α A : ℝ) (hα : 2 < α) (hA : 0 < A)
    (μ : EuclideanSpace ℝ (Fin m)) (Sig : Matrix (Fin m) (Fin m) ℝ) :
    ∃ c : ℝ, 1 < c ∧
      ∀ (P : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure P],
        HasMeanCov P μ Sig →
        ∫⁻ ξ, ENNReal.ofReal (Real.exp (‖ξ‖ ^ α)) ∂P ≤ ENNReal.ofReal A →
        ∀ (Ξ : Set (EuclideanSpace ℝ (Fin m))), IsClosed Ξ → P Ξᶜ = 0 →
        ∀ (L : Set (EuclideanSpace ℝ (Fin m) → EReal)), (∀ ℓ ∈ L, Measurable ℓ) →
        ∀ (N : ℕ), 0 < N → ∀ (η : ℝ), 0 < η → η < 1 →
        ∀ (ε : ℝ), Real.log (c / η) / Real.sqrt N ≤ ε →
        ∃ S : Set (Fin N → EuclideanSpace ℝ (Fin m)), MeasurableSet S ∧
          S ⊆ {ξh | ∀ ℓ ∈ L, risk P ℓ ≤ gelbrichRisk Ξ ε (sampleMean ξh) (sampleCov ξh) ℓ} ∧
          ENNReal.ofReal (1 - η) ≤ Measure.pi (fun _ : Fin N => P) S := by
  obtain ⟨c, hc, h21⟩ := theorem_21_concentration_mean_cov m α A hα hA μ Sig
  refine ⟨c, hc, ?_⟩
  intro P _ hP hmom Ξ _ hPΞ L _ N hN η hη0 hη1 ε hε
  obtain ⟨S, hS, hSsub, hSP⟩ := h21 P hP hmom N hN η hη0 hη1.le ε hε
  refine ⟨S, hS, ?_, hSP⟩
  intro ξh hξ ℓ _
  exact true_risk_le_gelbrich_risk Ξ ε (sampleMean ξh) (sampleCov ξh) P hPΞ μ Sig hP (hSsub hξ) ℓ

-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat27_triple_ext_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T10:22:04.584629+00:00
-- url     : https://prove2.me/submissions/3e772dea-3e03-460b-bae1-177f0b099b31

import Definitions.Def_LeanLevy_Levy_LevyKhintchineUniqueness
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_leanlevy_chat27_smeared_exponent_public
import Theorems.Thm_ProbabilityTheory_leanlevy_chat26b_smearedMeasure_finite_public
import Theorems.Thm_ProbabilityTheory_smearedMeasure_inj
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal Real

private lemma chat26_drift_eq_one {T T' : LevyKhintchineTriple}
    (hσ : T.gaussianVariance = T'.gaussianVariance)
    (hν : T.levyMeasure = T'.levyMeasure)
    (h : T.exponent 1 = T'.exponent 1) : T.drift = T'.drift := by
  rw [LevyKhintchineTriple.exponent, LevyKhintchineTriple.exponent, hσ, hν] at h
  have hI : (T.drift : ℂ) * Complex.I = (T'.drift : ℂ) * Complex.I := by
    have hcancel : (T.drift : ℂ) * ↑(1 : ℝ) * Complex.I
        = (T'.drift : ℂ) * ↑(1 : ℝ) * Complex.I := by linear_combination h
    simpa using hcancel
  exact Complex.ofReal_inj.mp (mul_right_cancel₀ Complex.I_ne_zero hI)

theorem solution {T T' : LevyKhintchineTriple}
    (h : ∀ ξ : ℝ, T.exponent ξ = T'.exponent ξ) : T = T' := by
  have hcf : charFun (smearedMeasure T.gaussianVariance T.levyMeasure)
      = charFun (smearedMeasure T'.gaussianVariance T'.levyMeasure) := by
    funext ξ
    rw [← leanlevy_chat27_smeared_exponent_public T ξ, ← leanlevy_chat27_smeared_exponent_public T' ξ, h ξ,
      intervalIntegral.integral_congr (fun u _ => h (ξ + u))]
  haveI : IsFiniteMeasure (smearedMeasure T.gaussianVariance T.levyMeasure) :=
    leanlevy_chat26b_smearedMeasure_finite_public
      T.gaussianVariance T.levyMeasure_isLevyMeasure
  haveI : IsFiniteMeasure (smearedMeasure T'.gaussianVariance T'.levyMeasure) :=
    leanlevy_chat26b_smearedMeasure_finite_public
      T'.gaussianVariance T'.levyMeasure_isLevyMeasure
  have hmeas := Measure.ext_of_charFun hcf
  obtain ⟨hσ, hν⟩ :=
    smearedMeasure_inj T.levyMeasure_isLevyMeasure
      T'.levyMeasure_isLevyMeasure hmeas
  have hdrift := chat26_drift_eq_one hσ hν (h 1)
  obtain ⟨b, σ, ν, hνfact⟩ := T
  obtain ⟨b', σ', ν', hνfact'⟩ := T'
  subst hσ; subst hν; subst hdrift; rfl
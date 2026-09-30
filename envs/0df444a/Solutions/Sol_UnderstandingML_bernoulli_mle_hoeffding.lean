-- Prove2me | solution 1 for UnderstandingML.bernoulli_mle_hoeffding
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T15:36:11.383251+00:00
-- url     : https://prove2.me/submissions/4f94a520-0519-48bc-9492-b754ecd8f926

import Definitions.Def_UnderstandingML_Generative
import Theorems.Thm_UnderstandingML_hoeffding_inequality

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

open UnderstandingML

private lemma bernoulliLaw_isProb {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (bernoulliLaw θ) := by
  constructor
  simp only [bernoulliLaw, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hθ.1 (by linarith [hθ.2])]
  simp

private lemma bernoulliLaw_integral {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    ∫ b, (if b then (1 : ℝ) else 0) ∂(bernoulliLaw θ) = θ := by
  have hfin : ∀ (c : ℝ) (b : Bool), IsFiniteMeasure (ENNReal.ofReal c • Measure.dirac b) :=
    fun c b ↦ ⟨by simp⟩
  unfold bernoulliLaw
  rw [integral_add_measure (Integrable.of_finite) (Integrable.of_finite),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  simp [ENNReal.toReal_ofReal hθ.1]

theorem solution (m : ℕ) (hm : 0 < m) (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    iidLaw (bernoulliLaw θ) m {S | Real.sqrt (Real.log (2 / δ) / (2 * m)) < |bernoulliMLE S - θ|} ≤
      ENNReal.ofReal δ := by
  haveI := bernoulliLaw_isProb hθ
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog : 0 < Real.log (2 / δ) :=
    Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  set ε := Real.sqrt (Real.log (2 / δ) / (2 * m)) with hε_def
  have hε : 0 < ε := Real.sqrt_pos.2 (by positivity)
  have H := hoeffding_inequality (bernoulliLaw θ) (fun b : Bool ↦ if b then (1 : ℝ) else 0)
    (measurable_of_countable _) (a := 0) (b := 1)
    (Filter.Eventually.of_forall fun b ↦ by cases b <;> simp) m hε
  rw [bernoulliLaw_integral hθ] at H
  have hε2 : ε ^ 2 = Real.log (2 / δ) / (2 * m) := Real.sq_sqrt (by positivity)
  have hexp : 2 * Real.exp (-(2 * m * ε ^ 2 / (1 - 0) ^ 2)) = δ := by
    rw [hε2]
    have : 2 * (m : ℝ) * (Real.log (2 / δ) / (2 * m)) / (1 - 0) ^ 2 = Real.log (2 / δ) := by
      norm_num; field_simp
    rw [this, Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  rw [hexp] at H
  exact H

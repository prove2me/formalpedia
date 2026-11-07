-- Prove2me | solution 1 for RogersSatchell.Unbiased.exp_time_mean
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T12:29:49.67271+00:00
-- url     : https://prove2.me/submissions/fc82a63a-771d-429c-932f-07480544d4d6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RogersSatchell_Unbiased_Process
import Theorems.Thm_RogersSatchell_Unbiased_exp_time_laws
import Theorems.Thm_RogersSatchell_Unbiased_wiener_hopf_split

open MeasureTheory ProbabilityTheory NNReal
open RogersSatchell.Unbiased

section
open Real Set

lemma expMeasure_integrable_and_mean {r : ℝ} (hr : 0 < r) :
    Integrable (fun x : ℝ => x) (expMeasure r) ∧ ∫ x, x ∂(expMeasure r) = 1 / r := by
  have hmeas : Measurable (gammaPDF 1 r) := by
    unfold gammaPDF; exact (measurable_gammaPDFReal 1 r).ennreal_ofReal
  have hlt : ∀ᵐ x ∂(volume : Measure ℝ), gammaPDF 1 r x < ⊤ :=
    ae_of_all _ fun x => by simp [gammaPDF]
  set g : ℝ → ℝ := fun x => (gammaPDF 1 r x).toReal • x with hg
  have hgx : ∀ x, g x = if 0 ≤ x then r * (x * exp (-(r * x))) else 0 := by
    intro x
    simp only [hg, gammaPDF, gammaPDFReal, smul_eq_mul]
    split_ifs with h
    · rw [ENNReal.toReal_ofReal (by positivity)]
      simp; ring
    · simp
  have hsupp : Function.support g ⊆ Ioi 0 := by
    intro x hx
    simp only [Function.mem_support, hgx] at hx
    split_ifs at hx with h
    · rcases h.lt_or_eq with h | h
      · exact h
      · subst h; simp at hx
    · exact absurd rfl hx
  have hon : IntegrableOn g (Ioi 0) := by
    have := (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := r)
      (by norm_num) one_pos hr).const_mul r
    refine IntegrableOn.congr_fun this (fun x (hx : 0 < x) => ?_) measurableSet_Ioi
    rw [hgx, if_pos hx.le]; simp
  have hint : Integrable g := (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
  have hval : ∫ x, g x = 1 / r := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0)]
    · rw [setIntegral_congr_fun measurableSet_Ioi
        (g := fun x => r * (x ^ ((2:ℝ) - 1) * exp (-(r * x))))]
      · rw [integral_const_mul, integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) hr]
        rw [Real.Gamma_two, Real.rpow_two]
        field_simp
      · intro x (hx : 0 < x)
        rw [hgx, if_pos hx.le]; norm_num
    · intro x hx
      by_contra h
      exact hx (hsupp h)
  refine ⟨?_, ?_⟩
  · unfold expMeasure gammaMeasure
    rw [integrable_withDensity_iff_integrable_smul' hmeas hlt]
    exact hint
  · unfold expMeasure gammaMeasure
    rw [integral_withDensity_eq_integral_toReal_smul hmeas hlt]
    exact hval

end

lemma hasLaw_exp_integrable_mean {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → ℝ} {r : ℝ} (hr : 0 < r) (hY : HasLaw Y (expMeasure r) P) :
    Integrable Y P ∧ ∫ ω, Y ω ∂P = 1 / r := by
  obtain ⟨hi, hm⟩ := expMeasure_integrable_and_mean hr
  refine ⟨?_, ?_⟩
  · have : Integrable (fun x : ℝ => x) (P.map Y) := by rw [hY.map_eq]; exact hi
    exact (integrable_map_measure aestronglyMeasurable_id hY.aemeasurable).mp this
  · rw [← hm]; exact hY.integral_eq

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hcont : ∀ ω, Continuous fun t => B t ω)
    (c σ : ℝ) (hσ : 0 < σ)
    (lam : ℝ) (hlam : 0 < lam) (T : Ω → ℝ) (hT : HasLaw T (expMeasure lam) P)
    (hTB : IndepFun T (fun ω => fun t => B t ω) P) :
    Integrable (fun ω => runMax σ c B (T ω).toNNReal ω *
      (runMax σ c B (T ω).toNNReal ω - logPrice σ c B (T ω).toNNReal ω)) P ∧
    ∫ ω, runMax σ c B (T ω).toNNReal ω *
      (runMax σ c B (T ω).toNNReal ω - logPrice σ c B (T ω).toNNReal ω) ∂P
      = 1 / (alpha σ c lam * RogersSatchell.Unbiased.beta σ c lam) ∧
    ∫ ω, runMax σ c B (T ω).toNNReal ω *
      (runMax σ c B (T ω).toNNReal ω - logPrice σ c B (T ω).toNNReal ω) ∂P
      = σ ^ 2 / (2 * lam) := by
  obtain ⟨hS, hI⟩ := exp_time_laws hB hcont c σ hσ lam hlam T hT hTB
  obtain ⟨hDm, -, hind, hmap⟩ := wiener_hopf_split hB hcont c σ hσ.le lam hlam T hT hTB
  have hD : HasLaw (fun ω => runMax σ c B (T ω).toNNReal ω - logPrice σ c B (T ω).toNNReal ω)
      (expMeasure (RogersSatchell.Unbiased.beta σ c lam)) P := ⟨hDm, hmap.trans hI.map_eq⟩
  -- positivity of the rates
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hsq : |c| < Real.sqrt (c ^ 2 + 2 * lam * σ ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg c) (by nlinarith [mul_pos hlam hσ2])
  have hα : 0 < alpha σ c lam := by
    unfold alpha; apply div_pos _ hσ2; linarith [le_abs_self c]
  have hβ : 0 < RogersSatchell.Unbiased.beta σ c lam := by
    unfold RogersSatchell.Unbiased.beta; apply div_pos _ hσ2; linarith [neg_abs_le c]
  have hαβ : alpha σ c lam * RogersSatchell.Unbiased.beta σ c lam = 2 * lam / σ ^ 2 := by
    unfold alpha RogersSatchell.Unbiased.beta
    have h0 : 0 ≤ c ^ 2 + 2 * lam * σ ^ 2 := by positivity
    have hs := Real.sq_sqrt h0
    field_simp
    nlinarith [hs]
  obtain ⟨hSi, hSm⟩ := hasLaw_exp_integrable_mean hα hS
  obtain ⟨hDi, hDmean⟩ := hasLaw_exp_integrable_mean hβ hD
  have hint := hind.integrable_mul hSi hDi
  have hE : ∫ ω, runMax σ c B (T ω).toNNReal ω *
      (runMax σ c B (T ω).toNNReal ω - logPrice σ c B (T ω).toNNReal ω) ∂P
      = 1 / (alpha σ c lam * RogersSatchell.Unbiased.beta σ c lam) := by
    rw [hind.integral_fun_mul_eq_mul_integral hSi.aestronglyMeasurable hDi.aestronglyMeasurable,
      hSm, hDmean]
    field_simp
  refine ⟨hint, hE, ?_⟩
  rw [hE, hαβ]
  field_simp

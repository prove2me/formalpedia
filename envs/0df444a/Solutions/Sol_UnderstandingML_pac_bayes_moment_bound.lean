-- Prove2me | solution 1 for UnderstandingML.pac_bayes_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-27T05:58:02.999844+00:00
-- url     : https://prove2.me/submissions/d29cdd25-23e6-4494-8ee2-9bfbb7d3db1f

import Definitions.Def_UnderstandingML_PACBayes
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open MeasureTheory ProbabilityTheory

namespace PACBayesMomentAux

open UnderstandingML

instance iidLaw_isProbabilityMeasure {Z : Type*} [MeasurableSpace Z] (D : Measure Z)
    [IsProbabilityMeasure D] (m : ℕ) : IsProbabilityMeasure (iidLaw D m) := by
  unfold iidLaw; infer_instance

theorem hoeffding_mgf_empRisk {Z Hyp : Type*} [MeasurableSpace Z] (loss : Hyp → Z → ℝ)
    (h : Hyp) (hmeas : Measurable (loss h)) (hloss : ∀ z, loss h z ∈ Set.Icc (0 : ℝ) 1)
    (D : Measure Z) [IsProbabilityMeasure D] (m : ℕ) (hm : 0 < m) (t : ℝ) :
    ∫ S, Real.exp (t * (risk loss D h - empRisk loss S h)) ∂(iidLaw D m) ≤
      Real.exp (t ^ 2 / (8 * m)) := by
  set μ := risk loss D h with hμ
  -- centered summands
  let X : Fin m → (Fin m → Z) → ℝ := fun i S ↦ μ - loss h (S i)
  have hind : iIndepFun X (iidLaw D m) := by
    have := iIndepFun_pi (μ := fun _ : Fin m ↦ D) (X := fun _ z ↦ μ - loss h z)
      (fun _ ↦ (measurable_const.sub hmeas).aemeasurable)
    exact this
  have hint : Integrable (loss h) D :=
    Integrable.of_mem_Icc 0 1 hmeas.aemeasurable (ae_of_all _ hloss)
  have hsub : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      HasSubgaussianMGF (X i) ((‖(μ : ℝ) - (μ - 1)‖₊ / 2) ^ 2) (iidLaw D m) := by
    intro i _
    apply hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    · exact ((measurable_const.sub hmeas).comp (measurable_pi_apply i)).aemeasurable
    · exact ae_of_all _ fun S ↦ ⟨by simp [X]; linarith [(hloss (S i)).2],
        by simp [X]; linarith [(hloss (S i)).1]⟩
    · have hmp : MeasurePreserving (fun S : Fin m → Z ↦ S i) (iidLaw D m) D :=
        measurePreserving_eval (fun _ ↦ D) i
      have : ∫ z, (μ - loss h z) ∂D = ∫ S, X i S ∂(iidLaw D m) := by
        conv_lhs => rw [← hmp.map_eq]
        rw [integral_map (measurable_pi_apply i).aemeasurable
          (measurable_const.sub hmeas).aestronglyMeasurable]
      rw [← this, integral_sub (integrable_const _) hint]
      simp [hμ, risk]
  have hsum := (HasSubgaussianMGF.sum_of_iIndepFun hind hsub).mgf_le (t / m)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have key : ∀ S : Fin m → Z, t * (μ - empRisk loss S h) = t / m * ∑ i, X i S := by
    intro S
    simp only [X, empRisk, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  simp_rw [key]
  refine le_trans hsum (le_of_eq ?_)
  congr 1
  have : ‖(μ : ℝ) - (μ - 1)‖₊ = 1 := by simp
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp
  ring

theorem gaussian_shift_integral (c : ℝ) :
    ∫ x : ℝ, Real.exp (-x ^ 2 + c * x) = Real.sqrt Real.pi * Real.exp (c ^ 2 / 4) := by
  have h1 : ∀ x : ℝ, Real.exp (-x ^ 2 + c * x) =
      Real.exp (c ^ 2 / 4) * Real.exp (-1 * (x - c / 2) ^ 2) := by
    intro x; rw [← Real.exp_add]; congr 1; ring
  simp_rw [h1]
  rw [integral_const_mul, integral_sub_right_eq_self (fun x ↦ Real.exp (-1 * x ^ 2)),
    integral_gaussian]
  simp [mul_comm]


theorem risk_mem_Icc {Z Hyp : Type*} [MeasurableSpace Z] (loss : Hyp → Z → ℝ) (h : Hyp)
    (hmeas : Measurable (loss h)) (hloss : ∀ z, loss h z ∈ Set.Icc (0 : ℝ) 1)
    (D : Measure Z) [IsProbabilityMeasure D] : risk loss D h ∈ Set.Icc (0 : ℝ) 1 := by
  have hint : Integrable (loss h) D :=
    Integrable.of_mem_Icc 0 1 hmeas.aemeasurable (ae_of_all _ hloss)
  refine ⟨integral_nonneg fun z ↦ (hloss z).1, ?_⟩
  calc risk loss D h = ∫ z, loss h z ∂D := rfl
    _ ≤ ∫ _z, (1 : ℝ) ∂D := integral_mono hint (integrable_const _) fun z ↦ (hloss z).2
    _ = 1 := by simp

theorem empRisk_mem_Icc {Z Hyp : Type*} (loss : Hyp → Z → ℝ) (h : Hyp)
    (hloss : ∀ z, loss h z ∈ Set.Icc (0 : ℝ) 1) {m : ℕ} (S : Fin m → Z) :
    empRisk loss S h ∈ Set.Icc (0 : ℝ) 1 := by
  unfold empRisk
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨div_nonneg (Finset.sum_nonneg fun i _ ↦ (hloss (S i)).1) hm'.le, ?_⟩
  rw [div_le_one hm']
  calc ∑ i, loss h (S i) ≤ ∑ _i : Fin m, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ (hloss (S i)).2
    _ = m := by simp

theorem abs_risk_sub_empRisk_le {Z Hyp : Type*} [MeasurableSpace Z] (loss : Hyp → Z → ℝ)
    (h : Hyp) (hmeas : Measurable (loss h)) (hloss : ∀ z, loss h z ∈ Set.Icc (0 : ℝ) 1)
    (D : Measure Z) [IsProbabilityMeasure D] {m : ℕ} (S : Fin m → Z) :
    |risk loss D h - empRisk loss S h| ≤ 1 := by
  have h1 := risk_mem_Icc loss h hmeas hloss D
  have h2 := empRisk_mem_Icc loss h hloss S
  rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end PACBayesMomentAux

open UnderstandingML PACBayesMomentAux in
theorem solution {Z Hyp : Type*} [MeasurableSpace Z] (loss : Hyp → Z → ℝ)
    (h : Hyp) (hmeas : Measurable (loss h)) (hloss : ∀ z, loss h z ∈ Set.Icc (0 : ℝ) 1)
    (D : Measure Z) [IsProbabilityMeasure D] (m : ℕ) (hm : 0 < m) :
    ∫ S, Real.exp (2 * (m - 1) * (risk loss D h - empRisk loss S h) ^ 2) ∂(iidLaw D m) ≤ m := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set a : ℝ := 2 * ((m : ℝ) - 1) with ha
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  set s : ℝ := Real.sqrt a with hs
  have hs2 : s ^ 2 = a := Real.sq_sqrt ha0
  set Δ : (Fin m → Z) → ℝ := fun S ↦ risk loss D h - empRisk loss S h with hΔdef
  have hΔ : ∀ S, |Δ S| ≤ 1 := fun S ↦ abs_risk_sub_empRisk_le loss h hmeas hloss D S
  have hΔm : Measurable Δ := by
    refine measurable_const.sub ?_
    unfold empRisk
    refine Measurable.div_const ?_ _
    exact Finset.measurable_sum _ fun i _ ↦ hmeas.comp (measurable_pi_apply i)
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  -- the Gaussian representation
  let F : (Fin m → Z) → ℝ → ℝ := fun S x ↦ Real.exp (-x ^ 2 + 2 * s * Δ S * x)
  have hrep : ∀ S, Real.exp (a * Δ S ^ 2) = (Real.sqrt Real.pi)⁻¹ * ∫ x, F S x := by
    intro S
    simp only [F]
    rw [gaussian_shift_integral, ← mul_assoc, inv_mul_cancel₀ hpi.ne', one_mul]
    congr 1
    rw [mul_pow, mul_pow, hs2]; ring
  have hFmeas : Measurable (Function.uncurry F) := by
    simp only [F, Function.uncurry_def]
    fun_prop
  have hFint : Integrable (Function.uncurry F) ((iidLaw D m).prod volume) := by
    have hg : Integrable (fun x : ℝ ↦ Real.exp (2 * s ^ 2) * Real.exp (-(1 / 2) * x ^ 2)) :=
      (integrable_exp_neg_mul_sq (by norm_num)).const_mul _
    refine (hg.comp_snd (iidLaw D m)).mono' hFmeas.aestronglyMeasurable (ae_of_all _ ?_)
    rintro ⟨S, x⟩
    simp only [F, Function.uncurry_apply_pair, Real.norm_eq_abs, Real.abs_exp]
    rw [← Real.exp_add, Real.exp_le_exp]
    have h1 : 2 * s * Δ S * x ≤ 2 * s * |x| := by
      have := hΔ S
      have hs0 : 0 ≤ s := Real.sqrt_nonneg _
      calc 2 * s * Δ S * x ≤ |2 * s * Δ S * x| := le_abs_self _
        _ = 2 * s * |Δ S| * |x| := by rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hs0]; norm_num
        _ ≤ 2 * s * 1 * |x| := by gcongr
        _ = 2 * s * |x| := by ring
    nlinarith [sq_abs x, sq_nonneg (|x| - 2 * s)]
  have hinner : ∀ x : ℝ, ∫ S, F S x ∂(iidLaw D m) ≤ Real.exp (-(1 / (m : ℝ)) * x ^ 2) := by
    intro x
    have : ∀ S, F S x = Real.exp (-x ^ 2) * Real.exp ((2 * s * x) * Δ S) := by
      intro S; simp only [F]; rw [← Real.exp_add]; ring_nf
    simp_rw [this]
    rw [integral_const_mul]
    calc Real.exp (-x ^ 2) * ∫ S, Real.exp ((2 * s * x) * Δ S) ∂(iidLaw D m)
        ≤ Real.exp (-x ^ 2) * Real.exp ((2 * s * x) ^ 2 / (8 * m)) := by
          gcongr
          exact hoeffding_mgf_empRisk loss h hmeas hloss D m hm _
      _ = Real.exp (-(1 / (m : ℝ)) * x ^ 2) := by
          rw [← Real.exp_add]; congr 1
          rw [mul_pow, mul_pow, hs2, ha]; field_simp; ring
  calc ∫ S, Real.exp (2 * (m - 1) * (risk loss D h - empRisk loss S h) ^ 2) ∂(iidLaw D m)
      = ∫ S, (Real.sqrt Real.pi)⁻¹ * (∫ x, F S x) ∂(iidLaw D m) := by
        refine integral_congr_ae (ae_of_all _ fun S ↦ ?_)
        simp only
        rw [← hrep S]
    _ = (Real.sqrt Real.pi)⁻¹ * ∫ x, ∫ S, F S x ∂(iidLaw D m) := by
        rw [integral_const_mul, integral_integral_swap hFint]
    _ ≤ (Real.sqrt Real.pi)⁻¹ * ∫ x : ℝ, Real.exp (-(1 / (m : ℝ)) * x ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hpi.le)
        refine integral_mono_of_nonneg (ae_of_all _ fun x ↦ ?_)
          (integrable_exp_neg_mul_sq (by positivity)) (ae_of_all _ hinner)
        exact integral_nonneg fun S ↦ (Real.exp_pos _).le
    _ = Real.sqrt m := by
        rw [integral_gaussian, div_div_eq_mul_div, div_one, Real.sqrt_mul Real.pi_pos.le,
          ← mul_assoc, inv_mul_cancel₀ hpi.ne', one_mul]
    _ ≤ m := by
        rw [Real.sqrt_le_iff]; constructor <;> nlinarith



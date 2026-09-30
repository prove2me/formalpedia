-- Prove2me | solution 1 for UnderstandingML.pac_bayes_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-27T05:58:54.13301+00:00
-- url     : https://prove2.me/submissions/ea37a6da-646d-4939-8078-3353539bda72

import Theorems.Thm_UnderstandingML_pac_bayes_moment_bound
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory

namespace PACBayesAux

open UnderstandingML

/-- Donsker–Varadhan change of measure for a bounded measurable `f`. -/
theorem donsker_varadhan {Hyp : Type*} [MeasurableSpace Hyp] (P Q : Measure Hyp)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hQP : Q ≪ P)
    (hlog : Integrable (fun h ↦ Real.log (Q.rnDeriv P h).toReal) Q)
    (f : Hyp → ℝ) (hf : Measurable f) (C : ℝ) (hfC : ∀ h, |f h| ≤ C) :
    ∫ h, f h ∂Q - klDiv Q P ≤ Real.log (∫ h, Real.exp (f h) ∂P) := by
  set ρ : Hyp → ℝ := fun h ↦ (Q.rnDeriv P h).toReal with hρ
  have hρm : Measurable ρ := (Measure.measurable_rnDeriv Q P).ennreal_toReal
  have hexpb : ∀ h, Real.exp (f h) ≤ Real.exp C := fun h ↦
    Real.exp_le_exp.2 (le_trans (le_abs_self _) (hfC h))
  have hexpint : ∀ (μ : Measure Hyp) [IsProbabilityMeasure μ],
      Integrable (fun h ↦ Real.exp (f h)) μ := by
    intro μ _
    refine Integrable.of_bound (C := Real.exp C) (hf.exp).aestronglyMeasurable
      (ae_of_all _ fun h ↦ ?_)
    rw [Real.norm_eq_abs, Real.abs_exp]; exact hexpb h
  have hfint : Integrable f Q := by
    refine Integrable.of_bound (C := C) hf.aestronglyMeasurable (ae_of_all _ fun h ↦ ?_)
    rw [Real.norm_eq_abs]; exact hfC h
  set Zc := ∫ h, Real.exp (f h) ∂P with hZc
  have hZpos : 0 < Zc := integral_exp_pos (hexpint P)
  let Y : Hyp → ℝ := fun h ↦ Real.exp (f h) * (ρ h)⁻¹
  have hρY : ∀ h, ρ h * Y h ≤ Real.exp (f h) := by
    intro h
    simp only [Y]
    by_cases h0 : ρ h = 0
    · rw [h0, zero_mul]; exact (Real.exp_pos _).le
    · rw [mul_comm, mul_assoc, inv_mul_cancel₀ h0, mul_one]
  have hρY0 : ∀ h, 0 ≤ ρ h * Y h := fun h ↦
    mul_nonneg ENNReal.toReal_nonneg (mul_nonneg (Real.exp_pos _).le
      (inv_nonneg.2 ENNReal.toReal_nonneg))
  have hρYint : Integrable (fun h ↦ ρ h * Y h) P := by
    refine Integrable.of_bound (C := Real.exp C)
      (hρm.mul ((hf.exp).mul hρm.inv)).aestronglyMeasurable (ae_of_all _ fun h ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hρY0 h)]
    exact (hρY h).trans (hexpb h)
  have hYint : Integrable Y Q := (integrable_toReal_rnDeriv_mul_iff hQP).1 hρYint
  have hYle : ∫ h, Y h ∂Q ≤ Zc := by
    rw [← integral_toReal_rnDeriv_mul hQP]
    exact integral_mono hρYint (hexpint P) hρY
  -- `ρ > 0` `Q`-a.e.
  have hρpos : ∀ᵐ h ∂Q, 0 < ρ h := by
    filter_upwards [Measure.rnDeriv_pos hQP, hQP.ae_le (Measure.rnDeriv_lt_top Q P)]
      with h h1 h2
    exact ENNReal.toReal_pos h1.ne' h2.ne
  have hpt : ∀ᵐ h ∂Q, f h - Real.log (ρ h) - Real.log Zc ≤ Y h / Zc - 1 := by
    filter_upwards [hρpos] with h hh
    have hx : 0 < Y h / Zc := div_pos (mul_pos (Real.exp_pos _) (inv_pos.2 hh)) hZpos
    have := Real.log_le_sub_one_of_pos hx
    rwa [Real.log_div (ne_of_gt (mul_pos (Real.exp_pos _) (inv_pos.2 hh))) hZpos.ne',
      Real.log_mul (Real.exp_pos _).ne' (inv_pos.2 hh).ne', Real.log_exp, Real.log_inv,
      ← sub_eq_add_neg] at this
  have hint1 : Integrable (fun h ↦ f h - Real.log (ρ h) - Real.log Zc) Q :=
    (hfint.sub hlog).sub (integrable_const _)
  have hint2 : Integrable (fun h ↦ Y h / Zc - 1) Q :=
    (hYint.div_const _).sub (integrable_const _)
  have hmono := integral_mono_ae hint1 hint2 hpt
  have e1 : ∫ h, (f h - Real.log (ρ h) - Real.log Zc) ∂Q =
      ∫ h, f h ∂Q - ∫ h, Real.log (ρ h) ∂Q - Real.log Zc := by
    have hlog' : Integrable (fun h ↦ Real.log (ρ h)) Q := hlog
    have hfl : Integrable (fun h ↦ f h - Real.log (ρ h)) Q := hfint.sub hlog'
    rw [integral_sub hfl (integrable_const _), integral_sub hfint hlog']
    simp
  have e2 : ∫ h, (Y h / Zc - 1) ∂Q = (∫ h, Y h ∂Q) / Zc - 1 := by
    rw [integral_sub (hYint.div_const _) (integrable_const _), integral_div]
    simp
  rw [e1, e2] at hmono
  have : (∫ h, Y h ∂Q) / Zc - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one hZpos]; exact hYle
  unfold klDiv
  linarith


instance iidLaw_isProbabilityMeasure' {Z : Type*} [MeasurableSpace Z] (D : Measure Z)
    [IsProbabilityMeasure D] (m : ℕ) : IsProbabilityMeasure (iidLaw D m) := by
  unfold iidLaw; infer_instance

theorem risk_mem_Icc' {Z Hyp : Type*} [MeasurableSpace Z] (loss : Hyp → Z → ℝ) (h : Hyp)
    (hmeas : Measurable (loss h)) (hloss : ∀ z, loss h z ∈ Set.Icc (0 : ℝ) 1)
    (D : Measure Z) [IsProbabilityMeasure D] : risk loss D h ∈ Set.Icc (0 : ℝ) 1 := by
  have hint : Integrable (loss h) D :=
    Integrable.of_mem_Icc 0 1 hmeas.aemeasurable (ae_of_all _ hloss)
  refine ⟨integral_nonneg fun z ↦ (hloss z).1, ?_⟩
  calc risk loss D h = ∫ z, loss h z ∂D := rfl
    _ ≤ ∫ _z, (1 : ℝ) ∂D := integral_mono hint (integrable_const _) fun z ↦ (hloss z).2
    _ = 1 := by simp

theorem empRisk_mem_Icc' {Z Hyp : Type*} (loss : Hyp → Z → ℝ) (h : Hyp)
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

theorem abs_risk_sub_empRisk_le' {Z Hyp : Type*} [MeasurableSpace Z] (loss : Hyp → Z → ℝ)
    (h : Hyp) (hmeas : Measurable (loss h)) (hloss : ∀ z, loss h z ∈ Set.Icc (0 : ℝ) 1)
    (D : Measure Z) [IsProbabilityMeasure D] {m : ℕ} (S : Fin m → Z) :
    |risk loss D h - empRisk loss S h| ≤ 1 := by
  have h1 := risk_mem_Icc' loss h hmeas hloss D
  have h2 := empRisk_mem_Icc' loss h hloss S
  rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Jensen's inequality for the square, for a bounded measurable function. -/
theorem sq_integral_le_integral_sq {Hyp : Type*} [MeasurableSpace Hyp] (Q : Measure Hyp)
    [IsProbabilityMeasure Q] (g : Hyp → ℝ) (hg : Measurable g) (hb : ∀ h, |g h| ≤ 1) :
    (∫ h, g h ∂Q) ^ 2 ≤ ∫ h, g h ^ 2 ∂Q := by
  have hgi : Integrable g Q :=
    Integrable.of_bound (C := 1) hg.aestronglyMeasurable (ae_of_all _ fun h ↦ by
      rw [Real.norm_eq_abs]; exact hb h)
  have hg2i : Integrable (fun h ↦ g h ^ 2) Q :=
    Integrable.of_bound (C := 1) (hg.pow_const 2).aestronglyMeasurable (ae_of_all _ fun h ↦ by
      rw [Real.norm_eq_abs, abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hb h))
  set c := ∫ h, g h ∂Q
  have h0 : 0 ≤ ∫ h, (g h - c) ^ 2 ∂Q := integral_nonneg fun h ↦ sq_nonneg _
  have hexp : ∀ h, (g h - c) ^ 2 = (g h ^ 2 - (2 * c) * g h) + c ^ 2 := fun h ↦ by ring
  simp_rw [hexp] at h0
  have hci : Integrable (fun h ↦ (2 * c) * g h) Q := hgi.const_mul _
  have hsi : Integrable (fun h ↦ g h ^ 2 - (2 * c) * g h) Q := hg2i.sub hci
  have e : ∫ h, (g h ^ 2 - (2 * c) * g h + c ^ 2) ∂Q = ∫ h, g h ^ 2 ∂Q - c ^ 2 := by
    rw [integral_add hsi (integrable_const _), integral_sub hg2i hci, integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  rw [e] at h0
  linarith

/-- The deterministic part of the proof of Theorem 31.1: on a sample for which the exponential
moment under the prior is below `B`, every admissible posterior satisfies the bound. -/
theorem bound_of_expMoment_lt {Z Hyp : Type*} [MeasurableSpace Z] [MeasurableSpace Hyp]
    (loss : Hyp → Z → ℝ) (hmeas : Measurable (Function.uncurry loss))
    (hloss : ∀ h z, loss h z ∈ Set.Icc (0 : ℝ) 1) (D : Measure Z) [IsProbabilityMeasure D]
    (P : Measure Hyp) [IsProbabilityMeasure P] {m : ℕ} (hm : 2 ≤ m) (S : Fin m → Z) (B : ℝ)
    (hB : ∫ h, Real.exp (2 * ((m : ℝ) - 1) * (risk loss D h - empRisk loss S h) ^ 2) ∂P < B)
    (Q : Measure Hyp) [IsProbabilityMeasure Q] (hQP : Q ≪ P)
    (hlog : Integrable (fun h ↦ Real.log (Q.rnDeriv P h).toReal) Q) :
    gibbsRisk loss D Q ≤
      gibbsEmpRisk loss S Q + Real.sqrt ((klDiv Q P + Real.log B) / (2 * (m - 1))) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  set a : ℝ := 2 * ((m : ℝ) - 1) with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have hlh : ∀ h, Measurable (loss h) := fun h ↦ hmeas.comp (measurable_const.prodMk measurable_id)
  have hrm : Measurable (fun h ↦ risk loss D h) :=
    (hmeas.stronglyMeasurable.integral_prod_right (ν := D)).measurable
  have hem : Measurable (fun h ↦ empRisk loss S h) := by
    unfold empRisk
    refine Measurable.div_const ?_ _
    exact Finset.measurable_sum _ fun i _ ↦ hmeas.comp (measurable_id.prodMk measurable_const)
  set Δ : Hyp → ℝ := fun h ↦ risk loss D h - empRisk loss S h with hΔ
  have hΔm : Measurable Δ := hrm.sub hem
  have hΔb : ∀ h, |Δ h| ≤ 1 := fun h ↦
    abs_risk_sub_empRisk_le' loss h (hlh h) (hloss h) D S
  have hri : Integrable (fun h ↦ risk loss D h) Q :=
    Integrable.of_bound (C := 1) hrm.aestronglyMeasurable (ae_of_all _ fun h ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (risk_mem_Icc' loss h (hlh h) (hloss h) D).1]
      exact (risk_mem_Icc' loss h (hlh h) (hloss h) D).2)
  have hei : Integrable (fun h ↦ empRisk loss S h) Q :=
    Integrable.of_bound (C := 1) hem.aestronglyMeasurable (ae_of_all _ fun h ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (empRisk_mem_Icc' loss h (hloss h) S).1]
      exact (empRisk_mem_Icc' loss h (hloss h) S).2)
  have hdiff : gibbsRisk loss D Q - gibbsEmpRisk loss S Q = ∫ h, Δ h ∂Q := by
    unfold gibbsRisk gibbsEmpRisk
    rw [← integral_sub hri hei]
  -- Donsker–Varadhan with `f = a Δ²`
  have hfb : ∀ h, |a * Δ h ^ 2| ≤ a := by
    intro h
    rw [abs_of_nonneg (mul_nonneg ha0.le (sq_nonneg _))]
    have : Δ h ^ 2 ≤ 1 := by
      rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (hΔb h)
    nlinarith
  have hdv := donsker_varadhan P Q hQP hlog (fun h ↦ a * Δ h ^ 2)
    (measurable_const.mul (hΔm.pow_const 2)) a hfb
  have hZpos : 0 < ∫ h, Real.exp (a * Δ h ^ 2) ∂P := by
    refine integral_exp_pos ?_
    refine Integrable.of_bound (C := Real.exp a)
      ((measurable_const.mul (hΔm.pow_const 2)).exp).aestronglyMeasurable
      (ae_of_all _ fun h ↦ ?_)
    rw [Real.norm_eq_abs, Real.abs_exp, Real.exp_le_exp]
    exact le_trans (le_abs_self _) (hfb h)
  have hlogB : Real.log (∫ h, Real.exp (a * Δ h ^ 2) ∂P) < Real.log B :=
    Real.log_lt_log hZpos hB
  have hjensen := sq_integral_le_integral_sq Q Δ hΔm hΔb
  rw [integral_const_mul] at hdv
  have key : a * (∫ h, Δ h ∂Q) ^ 2 < klDiv Q P + Real.log B := by nlinarith
  have hsq : ∫ h, Δ h ∂Q ≤ Real.sqrt ((klDiv Q P + Real.log B) / a) := by
    rcases le_or_gt (∫ h, Δ h ∂Q) 0 with hx | hx
    · exact hx.trans (Real.sqrt_nonneg _)
    · rw [Real.le_sqrt hx.le, le_div_iff₀ ha0]
      · linarith [mul_comm a ((∫ h, Δ h ∂Q) ^ 2)]
      · exact div_nonneg (by nlinarith [sq_nonneg (∫ h, Δ h ∂Q)]) ha0.le
  linarith

end PACBayesAux

open UnderstandingML PACBayesAux in
theorem solution {Z Hyp : Type*} [MeasurableSpace Z] [MeasurableSpace Hyp]
    (loss : Hyp → Z → ℝ) (hmeas : Measurable (Function.uncurry loss))
    (hloss : ∀ h z, loss h z ∈ Set.Icc (0 : ℝ) 1) (D : Measure Z) [IsProbabilityMeasure D]
    (P : Measure Hyp) [IsProbabilityMeasure P] (m : ℕ) (hm : 2 ≤ m) (δ : ℝ) (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    iidLaw D m {S | ∃ Q : Measure Hyp, IsProbabilityMeasure Q ∧ Q ≪ P ∧
      Integrable (fun h ↦ Real.log (Q.rnDeriv P h).toReal) Q ∧
      gibbsEmpRisk loss S Q + Real.sqrt ((klDiv Q P + Real.log (m / δ)) / (2 * (m - 1))) <
        gibbsRisk loss D Q} ≤ ENNReal.ofReal δ := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  set a : ℝ := 2 * ((m : ℝ) - 1) with ha
  have hlh : ∀ h, Measurable (loss h) := fun h ↦ hmeas.comp (measurable_const.prodMk measurable_id)
  have hrm : Measurable (fun h ↦ risk loss D h) :=
    (hmeas.stronglyMeasurable.integral_prod_right (ν := D)).measurable
  -- the exponential moment, as a function of the pair `(S, h)`
  let G : (Fin m → Z) × Hyp → ℝ := fun p ↦
    Real.exp (a * (risk loss D p.2 - empRisk loss p.1 p.2) ^ 2)
  have hGm : Measurable G := by
    refine (measurable_const.mul ((hrm.comp measurable_snd).sub ?_ |>.pow_const 2)).exp
    unfold empRisk
    refine Measurable.div_const ?_ _
    exact Finset.measurable_sum _ fun i _ ↦
      hmeas.comp (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst))
  have hGb : ∀ p, ‖G p‖ ≤ Real.exp a := by
    rintro ⟨S, h⟩
    simp only [G, Real.norm_eq_abs, Real.abs_exp, Real.exp_le_exp]
    have h1 := abs_risk_sub_empRisk_le' loss h (hlh h) (hloss h) D S
    have : (risk loss D h - empRisk loss S h) ^ 2 ≤ 1 := by
      rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) h1
    have ha0 : 0 ≤ a := by rw [ha]; linarith
    nlinarith
  have hGpos : ∀ p, 0 ≤ G p := fun p ↦ (Real.exp_pos _).le
  let F : (Fin m → Z) → ENNReal := fun S ↦ ∫⁻ h, ENNReal.ofReal (G (S, h)) ∂P
  have hFm : Measurable F := (ENNReal.measurable_ofReal.comp hGm).lintegral_prod_right'
  have hGintP : ∀ S, Integrable (fun h ↦ G (S, h)) P := fun S ↦
    Integrable.of_bound (C := Real.exp a)
      (hGm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (ae_of_all _ fun h ↦ hGb (S, h))
  have hGintS : ∀ h, Integrable (fun S ↦ G (S, h)) (iidLaw D m) := fun h ↦
    Integrable.of_bound (C := Real.exp a)
      (hGm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (ae_of_all _ fun S ↦ hGb (S, h))
  have hFeq : ∀ S, F S = ENNReal.ofReal (∫ h, G (S, h) ∂P) := fun S ↦
    (ofReal_integral_eq_lintegral_ofReal (hGintP S) (ae_of_all _ fun h ↦ hGpos _)).symm
  -- expectation of `F`
  have hFint : ∫⁻ S, F S ∂(iidLaw D m) ≤ ENNReal.ofReal m := by
    simp only [F]
    rw [lintegral_lintegral_swap (f := fun S h ↦ ENNReal.ofReal (G (S, h)))
      ((ENNReal.measurable_ofReal.comp hGm).aemeasurable)]
    calc ∫⁻ h, ∫⁻ S, ENNReal.ofReal (G (S, h)) ∂(iidLaw D m) ∂P
        ≤ ∫⁻ _h, ENNReal.ofReal m ∂P := by
          refine lintegral_mono fun h ↦ ?_
          rw [← ofReal_integral_eq_lintegral_ofReal (hGintS h) (ae_of_all _ fun S ↦ hGpos _)]
          exact ENNReal.ofReal_le_ofReal
            (pac_bayes_moment_bound loss h (hlh h) (hloss h) D m (by omega))
      _ = ENNReal.ofReal m := by simp
  -- Markov's inequality
  have hmδ : (0 : ℝ) < m / δ := div_pos hm0 hδ
  have hmarkov : iidLaw D m {S | ENNReal.ofReal (m / δ) ≤ F S} ≤ ENNReal.ofReal δ := by
    refine (meas_ge_le_lintegral_div hFm.aemeasurable
      (ENNReal.ofReal_pos.2 hmδ).ne' ENNReal.ofReal_ne_top).trans ?_
    calc (∫⁻ S, F S ∂(iidLaw D m)) / ENNReal.ofReal (m / δ)
        ≤ ENNReal.ofReal m / ENNReal.ofReal (m / δ) := by gcongr
      _ = ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_div_of_pos hmδ]
          congr 1
          field_simp
  refine le_trans (measure_mono ?_) hmarkov
  rintro S ⟨Q, hQ, hQP, hlog, hlt⟩
  show ENNReal.ofReal (m / δ) ≤ F S
  refine le_of_not_gt fun hS ↦ ?_
  rw [hFeq, ENNReal.ofReal_lt_ofReal_iff hmδ] at hS
  have := bound_of_expMoment_lt loss hmeas hloss D P hm S (m / δ) hS Q hQP hlog
  linarith

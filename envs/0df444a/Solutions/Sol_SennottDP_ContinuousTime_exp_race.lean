-- Prove2me | solution 1 for SennottDP.ContinuousTime.exp_race
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T07:37:31.888985+00:00
-- url     : https://prove2.me/submissions/f521b656-50c1-4e1a-849f-6e7f08b6d6e2

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

namespace E150656C

lemma expIoi (r : ℝ) (hr : 0 < r) (t : ℝ) :
    expMeasure r (Set.Ioi t) = ENNReal.ofReal (if 0 ≤ t then Real.exp (-(r * t)) else 1) := by
  have := isProbabilityMeasure_expMeasure hr
  have h2 : (expMeasure r).real (Set.Ioi t) = (if 0 ≤ t then Real.exp (-(r * t)) else 1) := by
    have hc : (Set.Iic t)ᶜ = Set.Ioi t := Set.compl_Iic
    rw [← hc, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real,
      cdf_expMeasure_eq hr]
    split_ifs <;> ring
  rw [← h2, ofReal_measureReal]

lemma cdfP {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (μ : ℝ) (hμ : 0 < μ) (hX : Measurable X) (hlaw : P.map X = expMeasure μ)
    (t : ℝ) (ht : 0 ≤ t) :
    (P {ω | X ω ≤ t}).toReal = 1 - Real.exp (-(μ * t)) := by
  have := isProbabilityMeasure_expMeasure hμ
  have h1 : P {ω | X ω ≤ t} = expMeasure μ (Set.Iic t) := by
    rw [← hlaw, Measure.map_apply hX measurableSet_Iic]; rfl
  rw [h1, ← measureReal_def, ← cdf_eq_real, cdf_expMeasure_eq hμ, if_pos ht]

lemma hd (μ : ℝ) : HasDerivAt (fun δ : ℝ => 1 - Real.exp (-(μ * δ))) μ 0 := by
  have h0 := (hasDerivAt_neg_exp_mul_exp (r := μ) (x := 0)).const_add 1
  have e : (fun δ : ℝ => 1 - Real.exp (-(μ * δ))) = fun a => 1 + -Real.exp (-(μ * a)) := by
    funext a; ring
  rw [e]
  exact h0.congr_deriv (by simp)

lemma part1 (μ₁ μ₂ : ℝ) :
    (fun δ : ℝ => (1 - Real.exp (-(μ₁ * δ))) * (1 - Real.exp (-(μ₂ * δ))))
      =o[𝓝 (0 : ℝ)] (fun δ : ℝ => δ) := by
  have h1 := (hd μ₁).isBigO_sub
  simp only [mul_zero, neg_zero, Real.exp_zero, sub_self, sub_zero] at h1
  have hc : Continuous (fun δ : ℝ => 1 - Real.exp (-(μ₂ * δ))) := by fun_prop
  have h2 : Tendsto (fun δ : ℝ => 1 - Real.exp (-(μ₂ * δ))) (𝓝 0) (𝓝 0) := by
    have := hc.tendsto 0
    simpa using this
  have h2' := (isLittleO_one_iff ℝ).2 h2
  have := h1.mul_isLittleO h2'
  simpa using this

end E150656C

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics in
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₁ X₂ : Ω → ℝ) (μ₁ μ₂ : ℝ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hlaw₁ : P.map X₁ = expMeasure μ₁) (hlaw₂ : P.map X₂ = expMeasure μ₂)
    (hindep : IndepFun X₁ X₂ P) :
    (fun δ : ℝ => (P {ω | X₁ ω ≤ δ ∧ X₂ ω ≤ δ}).toReal) =o[𝓝[>] (0 : ℝ)] (fun δ : ℝ => δ) ∧
      P {ω | X₁ ω < X₂ ω} = ENNReal.ofReal (μ₁ / (μ₁ + μ₂)) ∧
      P.map (fun ω => min (X₁ ω) (X₂ ω)) = expMeasure (μ₁ + μ₂) := by
  have hP1 := isProbabilityMeasure_expMeasure hμ₁
  have hP2 := isProbabilityMeasure_expMeasure hμ₂
  have hP12 := isProbabilityMeasure_expMeasure (add_pos hμ₁ hμ₂)
  refine ⟨?_, ?_, ?_⟩
  · -- part 1
    have ho := (E150656C.part1 μ₁ μ₂).mono (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    refine ho.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hset : {ω | X₁ ω ≤ δ ∧ X₂ ω ≤ δ} = X₁ ⁻¹' Set.Iic δ ∩ X₂ ⁻¹' Set.Iic δ := rfl
    rw [hset, hindep.measure_inter_preimage_eq_mul _ _ measurableSet_Iic measurableSet_Iic,
      ENNReal.toReal_mul]
    have e1 := E150656C.cdfP P X₁ μ₁ hμ₁ hX₁ hlaw₁ δ (le_of_lt hδ)
    have e2 := E150656C.cdfP P X₂ μ₂ hμ₂ hX₂ hlaw₂ δ (le_of_lt hδ)
    rw [show X₁ ⁻¹' Set.Iic δ = {ω | X₁ ω ≤ δ} from rfl,
      show X₂ ⁻¹' Set.Iic δ = {ω | X₂ ω ≤ δ} from rfl, e1, e2]
  · -- part 2
    have hmap : P.map (fun ω => (X₁ ω, X₂ ω)) = (expMeasure μ₁).prod (expMeasure μ₂) := by
      rw [← hlaw₁, ← hlaw₂]
      exact (indepFun_iff_map_prod_eq_prod_map_map hX₁.aemeasurable hX₂.aemeasurable).1 hindep
    have hS : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} := measurableSet_lt measurable_fst measurable_snd
    have h1 : P {ω | X₁ ω < X₂ ω} = P.map (fun ω => (X₁ ω, X₂ ω)) {p : ℝ × ℝ | p.1 < p.2} := by
      rw [Measure.map_apply (hX₁.prodMk hX₂) hS]; rfl
    rw [h1, hmap, Measure.prod_apply hS]
    have hE : expMeasure μ₁ = volume.withDensity (exponentialPDF μ₁) := rfl
    have hm1 : Measurable (exponentialPDF μ₁) := (measurable_exponentialPDFReal μ₁).ennreal_ofReal
    have hm12 : Measurable (exponentialPDF (μ₁ + μ₂)) :=
      (measurable_exponentialPDFReal (μ₁ + μ₂)).ennreal_ofReal
    rw [hE, lintegral_withDensity_eq_lintegral_mul _ hm1 (measurable_measure_prodMk_left hS)]
    have hpt : ∀ x : ℝ, (exponentialPDF μ₁ * fun x => expMeasure μ₂ (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 < p.2})) x
        = ENNReal.ofReal (μ₁ / (μ₁ + μ₂)) * exponentialPDF (μ₁ + μ₂) x := by
      intro x
      have hpre : Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 < p.2} = Set.Ioi x := rfl
      simp only [Pi.mul_apply, hpre, E150656C.expIoi μ₂ hμ₂ x]
      rcases lt_or_ge x 0 with hx | hx
      · rw [exponentialPDF_of_neg hx, exponentialPDF_of_neg hx]; simp
      · rw [exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg hx, if_pos hx,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have hne : μ₁ + μ₂ ≠ 0 := (add_pos hμ₁ hμ₂).ne'
        rw [mul_assoc, ← Real.exp_add]
        field_simp
        ring_nf
    simp_rw [hpt]
    rw [lintegral_const_mul _ hm12,
      lintegral_exponentialPDF_eq_one (add_pos hμ₁ hμ₂), mul_one]
  · -- part 3
    have hmin : Measurable (fun ω => min (X₁ ω) (X₂ ω)) := hX₁.min hX₂
    have : IsProbabilityMeasure (P.map (fun ω => min (X₁ ω) (X₂ ω))) :=
      Measure.isProbabilityMeasure_map hmin.aemeasurable
    refine Measure.ext_of_Iic _ _ fun t => ?_
    rw [← Set.compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi,
      prob_compl_eq_one_sub measurableSet_Ioi]
    congr 1
    rw [Measure.map_apply hmin measurableSet_Ioi]
    have hset : (fun ω => min (X₁ ω) (X₂ ω)) ⁻¹' Set.Ioi t = X₁ ⁻¹' Set.Ioi t ∩ X₂ ⁻¹' Set.Ioi t := by
      ext ω; simp
    rw [hset, hindep.measure_inter_preimage_eq_mul _ _ measurableSet_Ioi measurableSet_Ioi,
      ← Measure.map_apply hX₁ measurableSet_Ioi, ← Measure.map_apply hX₂ measurableSet_Ioi,
      hlaw₁, hlaw₂, E150656C.expIoi μ₁ hμ₁, E150656C.expIoi μ₂ hμ₂,
      E150656C.expIoi _ (add_pos hμ₁ hμ₂), ← ENNReal.ofReal_mul (by split_ifs <;> positivity)]
    congr 1
    split_ifs
    · rw [← Real.exp_add]; ring_nf
    · simp

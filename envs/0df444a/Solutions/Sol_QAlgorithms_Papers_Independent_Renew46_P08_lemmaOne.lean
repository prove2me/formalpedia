-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P08.lemmaOne
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:14:00.370356+00:00
-- url     : https://prove2.me/submissions/1da71c83-a444-40d3-bad5-54f41eba8ba6

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P08
noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Renew46.P08

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (CountableStateEnsemble convexOperatorMixture)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity traceSize tensorApply productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble averageCoefficients extendedEntropyNats
    extendedRelativeEntropyNats ensembleHolevo)

open QAlgorithms.Papers.Independent.Frontier18.P08
  (partialTraceFirst partialTraceSecond operatorTrace)

open QAlgorithms.Papers.Independent.Frontier30.P14 (conjugateKernel)

open QAlgorithms.Papers.Independent.Claimed50.P07
  (boundedCoefficients oscillatorGround oscillatorLevels oscillatorEnvelope oscillatorEntropyBounded)

open QAlgorithms.Papers.Independent.Next46.P08 (continuityRatio MajorantRegularity)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)


lemma g66a_optF_ge (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1) : 1 ≤ optimizationFactor t := by
  unfold optimizationFactor
  have : 1 ≤ (1 + t / 2) / (1 - t) := by rw [le_div_iff₀ (by linarith)]; linarith
  linarith

lemma g66a_littleO (b c : ℝ) :
    Asymptotics.IsLittleO atTop
      (fun x : ℝ => optimizationFactor (1 / x) * (x - b * Real.log (1 / x) + c) - x) (fun x : ℝ => x) := by
  have ht : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hf : Tendsto (fun x : ℝ => optimizationFactor (1 / x)) atTop (𝓝 1) := by
    have hc : ContinuousAt (fun t : ℝ => 2 * t + (1 + t / 2) / (1 - t)) 0 := by
      apply ContinuousAt.add (by fun_prop)
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      simp
    have := hc.tendsto.comp ht
    simpa [optimizationFactor, Function.comp_def] using this
  have hlim : Tendsto (fun x : ℝ => optimizationFactor (1 / x) *
      (1 + b * (Real.log x / x) + c * (1 / x)) - 1) atTop (𝓝 0) := by
    have := (hf.mul (((tendsto_const_nhds (x := (1:ℝ))).add
      ((tendsto_const_nhds (x := b)).mul hlog)).add ((tendsto_const_nhds (x := c)).mul ht))).sub
      (tendsto_const_nhds (x := (1:ℝ)))
    simpa using this
  rw [Asymptotics.isLittleO_iff_tendsto']
  · refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [one_div, Real.log_inv]
    field_simp
    ring
  · filter_upwards [eventually_gt_atTop 0] with x hx h0
    exact absurd h0 hx.ne'

theorem g66a_lemmaOne (b c : ℝ) (hb : 0 < b) :
    ∃ R : ℝ → ℝ, Asymptotics.IsLittleO atTop R (fun x : ℝ => x) ∧
      ∀ᶠ x : ℝ in atTop, ∃ t : ℝ, t ∈ Set.Ioo 0 (1/2 : ℝ) ∧
        (∀ s ∈ Set.Ioo 0 (1/2 : ℝ),
          optimizationFactor t * (x - b * Real.log t + c) ≤
            optimizationFactor s * (x - b * Real.log s + c)) ∧
        optimizationFactor t * (x - b * Real.log t + c) ≤ x + R x := by
  refine ⟨_, g66a_littleO b c, ?_⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  filter_upwards [eventually_ge_atTop (10 * (|c| + b * Real.log 8) + 10)] with x hx
  have hc1 := le_abs_self c
  have hc2 := neg_abs_le c
  have hbl : 0 < b * Real.log 2 := mul_pos hb hl2
  have hb8 : 0 ≤ b * Real.log 8 := by rw [hl8]; nlinarith
  set φ : ℝ → ℝ := fun t => optimizationFactor t * (x - b * Real.log t + c) with hφ
  set a := Real.exp (-(2 * x / b)) with ha
  have ha0 : 0 < a := Real.exp_pos _
  have hloga : Real.log a = -(2 * x / b) := Real.log_exp _
  have ha8 : a < 1 / 8 := by
    rw [ha, show (1:ℝ) / 8 = Real.exp (-Real.log 8) by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num]
    apply Real.exp_lt_exp.mpr
    rw [neg_lt_neg_iff, lt_div_iff₀ hb]
    nlinarith
  have hf8 : optimizationFactor (1/8) = 41 / 28 := by unfold optimizationFactor; norm_num
  have hf2 : optimizationFactor (1/2) = 7 / 2 := by unfold optimizationFactor; norm_num
  have hφ8 : φ (1/8) = 41 / 28 * (x + b * Real.log 8 + c) := by
    simp only [hφ]; rw [hf8, one_div, Real.log_inv]; ring
  have hφ2 : φ (1/2) = 7 / 2 * (x + b * Real.log 2 + c) := by
    simp only [hφ]; rw [hf2, one_div, Real.log_inv]; ring
  have hcont : ContinuousOn φ (Set.Icc a (1/2)) := by
    apply ContinuousOn.mul
    · unfold optimizationFactor
      apply ContinuousOn.add (by fun_prop)
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro t ht; have := ht.2; norm_num at this; linarith
    · apply ContinuousOn.add _ continuousOn_const
      apply ContinuousOn.sub continuousOn_const
      apply ContinuousOn.mul continuousOn_const
      apply Real.continuousOn_log.mono
      intro t ht; have := ht.1; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith
  obtain ⟨t, ht, hmin⟩ := (isCompact_Icc).exists_isMinOn
    (Set.nonempty_Icc.mpr (by linarith)) hcont
  have h8mem : (1/8 : ℝ) ∈ Set.Icc a (1/2) := ⟨ha8.le, by norm_num⟩
  have ht8 : φ t ≤ φ (1/8) := hmin h8mem
  have hlt2 : φ (1/8) < φ (1/2) := by
    rw [hφ8, hφ2, hl8]; nlinarith
  have htne : t ≠ 1/2 := by
    rintro rfl; linarith
  have htI : t ∈ Set.Ioo 0 (1/2 : ℝ) := ⟨lt_of_lt_of_le ha0 ht.1, lt_of_le_of_ne ht.2 htne⟩
  have hallmin : ∀ s ∈ Set.Ioo 0 (1/2 : ℝ), φ t ≤ φ s := by
    intro s hs
    by_cases hsa : a ≤ s
    · exact hmin ⟨hsa, hs.2.le⟩
    · push Not at hsa
      have hlogs : Real.log s < Real.log a := Real.log_lt_log hs.1 hsa
      have hbr : x - b * Real.log a + c ≤ x - b * Real.log s + c := by nlinarith
      have hbr2 : x - b * Real.log a + c = 3 * x + c := by
        rw [hloga]; field_simp; ring
      have hf1 := g66a_optF_ge s hs.1.le (by linarith [hs.2])
      have hpos : 0 ≤ x - b * Real.log s + c := by linarith
      have : x - b * Real.log s + c ≤ φ s := by
        simp only [hφ]; nlinarith
      have h3 : φ (1/8) ≤ 3 * x + c := by rw [hφ8, hl8]; nlinarith
      linarith
  refine ⟨t, htI, hallmin, ?_⟩
  have hx2 : (1 / x) ∈ Set.Ioo 0 (1/2 : ℝ) := by
    have hxp : 0 < x := by nlinarith
    refine ⟨by positivity, ?_⟩
    rw [div_lt_div_iff₀ hxp (by norm_num)]; nlinarith
  have := hallmin _ hx2
  simp only [hφ] at this
  linarith

/-- Lemma 1, PDF p.17: attained scalar minimum and x+o(x) bound only
EVENTUALLY as x tends to infinity, on the printed OPEN interval (0,1/2). -/
theorem solution (b c : ℝ) (hb : 0 < b) :
    ∃ R : ℝ → ℝ, Asymptotics.IsLittleO atTop R (fun x : ℝ => x) ∧
      ∀ᶠ x : ℝ in atTop, ∃ t : ℝ, t ∈ Set.Ioo 0 (1/2 : ℝ) ∧
        (∀ s ∈ Set.Ioo 0 (1/2 : ℝ),
          optimizationFactor t * (x - b * Real.log t + c) ≤
            optimizationFactor s * (x - b * Real.log s + c)) ∧
        optimizationFactor t * (x - b * Real.log t + c) ≤ x + R x := g66a_lemmaOne b c hb


end

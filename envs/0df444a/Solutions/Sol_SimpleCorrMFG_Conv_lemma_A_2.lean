-- Prove2me | solution 1 for SimpleCorrMFG.Conv.lemma_A_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T06:25:08.83784+00:00
-- url     : https://prove2.me/submissions/68e226c0-27cc-4929-b3d7-a3fdedb3ec59

import Mathlib

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

theorem solution {𝒴 𝒵 : Type*} [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴]
    [BorelSpace 𝒴] [MetricSpace 𝒵] [PolishSpace 𝒵] [MeasurableSpace 𝒵] [BorelSpace 𝒵]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    (Yn : ∀ n, Ω n → 𝒴) (Zn Ztn : ∀ n, Ω n → 𝒵) (hYn : ∀ n, Measurable (Yn n))
    (hZn : ∀ n, Measurable (Zn n)) (hZtn : ∀ n, Measurable (Ztn n))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → 𝒴) (Z : Ω' → 𝒵) (hY : Measurable Y) (hZ : Measurable Z)
    (hconv : TendstoInDistribution (fun n ω => (Yn n ω, Zn n ω)) atTop (fun ω => (Y ω, Z ω)) P P')
    (hdist : Tendsto (fun n => ∫⁻ ω, edist (Zn n ω) (Ztn n ω) ∂(P n)) atTop (𝓝 0)) :
    TendstoInDistribution (fun n ω => (Yn n ω, Ztn n ω)) atTop (fun ω => (Y ω, Z ω)) P P' := by
  letI : MetricSpace 𝒴 := TopologicalSpace.completelyMetrizableMetric 𝒴
  have hm : ∀ n, Measurable (fun ω => (Yn n ω, Ztn n ω)) := fun n => (hYn n).prodMk (hZtn n)
  have hm0 : ∀ n, Measurable (fun ω => (Yn n ω, Zn n ω)) := fun n => (hYn n).prodMk (hZn n)
  have hmY : Measurable (fun ω => (Y ω, Z ω)) := hY.prodMk hZ
  refine ⟨fun n => (hm n).aemeasurable, hmY.aemeasurable, ?_⟩
  have h0 := (tendsto_iff_forall_lipschitz_integral_tendsto (Ω := 𝒴 × 𝒵)).mp hconv.tendsto
  refine (tendsto_iff_forall_lipschitz_integral_tendsto (Ω := 𝒴 × 𝒵)).mpr ?_
  intro F hFb hFl
  obtain ⟨C, hC⟩ := hFb
  obtain ⟨L, hL⟩ := hFl
  have hFc : Continuous F := hL.continuous
  have hlim := h0 F ⟨C, hC⟩ ⟨L, hL⟩
  simp only [ProbabilityMeasure.coe_mk] at hlim ⊢
  rw [integral_map hmY.aemeasurable hFc.aestronglyMeasurable] at hlim ⊢
  simp_rw [integral_map (hm _).aemeasurable hFc.aestronglyMeasurable]
  simp_rw [integral_map (hm0 _).aemeasurable hFc.aestronglyMeasurable] at hlim
  -- integrability of bounded continuous compositions
  have hint : ∀ n (A : Ω n → 𝒴 × 𝒵), Measurable A → Integrable (fun ω => F (A ω)) (P n) := by
    intro n A hA
    obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure (P n)
    refine Integrable.of_bound (hFc.comp_aestronglyMeasurable hA.aestronglyMeasurable)
      (‖F (A ω₀)‖ + C) (ae_of_all _ fun ω => ?_)
    have := hC (A ω) (A ω₀)
    rw [Real.dist_eq] at this
    have h2 := abs_sub_abs_le_abs_sub (F (A ω)) (F (A ω₀))
    simp only [Real.norm_eq_abs]
    linarith
  -- the difference of the two sequences of integrals tends to zero
  set d : ℕ → ℝ := fun n => ∫ ω, F (Yn n ω, Ztn n ω) ∂(P n) - ∫ ω, F (Yn n ω, Zn n ω) ∂(P n)
  have hd : ∀ n, ‖d n‖ₑ ≤ (L : ENNReal) * ∫⁻ ω, edist (Zn n ω) (Ztn n ω) ∂(P n) := by
    intro n
    simp only [d]
    rw [← integral_sub (hint n _ (hm n)) (hint n _ (hm0 n))]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    refine lintegral_mono fun ω => ?_
    rw [← edist_eq_enorm_sub]
    refine (hL _ _).trans ?_
    gcongr
    rw [Prod.edist_eq, edist_self, zero_max, edist_comm]
  have hd0 : Tendsto d atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ‖d n‖ₑ) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n => (L : ENNReal) * ∫⁻ ω, edist (Zn n ω) (Ztn n ω) ∂(P n)) atTop
          (𝓝 ((L : ENNReal) * 0)) := ENNReal.Tendsto.const_mul hdist (Or.inr ENNReal.coe_ne_top)
      rw [mul_zero] at h2
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun n => zero_le) hd
    exact tendsto_zero_iff_enorm_tendsto_zero.mpr h1
  have := hd0.add hlim
  simp only [zero_add, d, sub_add_cancel] at this
  exact this

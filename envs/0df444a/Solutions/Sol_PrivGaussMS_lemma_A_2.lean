-- Prove2me | solution 1 for PrivGaussMS.lemma_A_2
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T16:54:20.594809+00:00
-- url     : https://prove2.me/submissions/1c0f4b9f-de5f-4183-bf8f-3d839bd1d75e

import Mathlib
import Definitions.Def_PrivGaussMS_Basics

open MeasureTheory ProbabilityTheory

namespace SolPrivGaussMSA2

/-- The real-valued DP inequality on events, read in `ℝ≥0∞`. -/
lemma ennreal_of_real_ineq {Y : Type*} [MeasurableSpace Y] (μ μ' : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] (ε δ : ℝ) (hδ : 0 ≤ δ) {O : Set Y}
    (h : μ.real O ≤ Real.exp ε * μ'.real O + δ) :
    μ O ≤ ENNReal.ofReal (Real.exp ε) * μ' O + ENNReal.ofReal δ := by
  have := ENNReal.ofReal_le_ofReal h
  rwa [ENNReal.ofReal_add (mul_nonneg (Real.exp_pos ε).le measureReal_nonneg) hδ,
    ENNReal.ofReal_mul (Real.exp_pos ε).le, measureReal_def, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_toReal (measure_ne_top _ _)]
    at this

/-- Back from `ℝ≥0∞` to the real-valued DP inequality. -/
lemma real_of_ennreal_ineq {a b : ENNReal} (e δ : ℝ) (he : 0 ≤ e) (hδ : 0 ≤ δ) (hb : b ≠ ⊤)
    (h : a ≤ ENNReal.ofReal e * b + ENNReal.ofReal δ) :
    a.toReal ≤ e * b.toReal + δ := by
  have hne : ENNReal.ofReal e * b + ENNReal.ofReal δ ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb, ENNReal.ofReal_ne_top⟩
  have h4 := ENNReal.toReal_mono hne h
  rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb) ENNReal.ofReal_ne_top,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal he, ENNReal.toReal_ofReal hδ] at h4

/-- The event-wise DP inequality extends to `[0,1]`-valued test functions (layer cake). -/
lemma dp_fun {Y : Type*} [MeasurableSpace Y] (μ μ' : Measure Y)
    (c d : ENNReal) (hE : ∀ O, MeasurableSet O → μ O ≤ c * μ' O + d)
    (f : Y → ENNReal) (hf : Measurable f) (hf1 : ∀ y, f y ≤ 1) :
    ∫⁻ y, f y ∂μ ≤ c * ∫⁻ y, f y ∂μ' + d := by
  set g : Y → ℝ := fun y => (f y).toReal with hg_def
  have hg : Measurable g := hf.ennreal_toReal
  have hfg : ∀ y, f y = ENNReal.ofReal (g y) := fun y =>
    (ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hf1 y))).symm
  have hg1 : ∀ y, g y ≤ 1 := fun y => by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (hf1 y)
    simpa [hg_def] using this
  have hg0 : ∀ y, 0 ≤ g y := fun y => ENNReal.toReal_nonneg
  have layer : ∀ ν : Measure Y, ∫⁻ y, f y ∂ν = ∫⁻ t in Set.Ioi 0, ν {a | t < g a} := by
    intro ν
    simp_rw [hfg]
    exact lintegral_eq_lintegral_meas_lt ν (Filter.Eventually.of_forall hg0) hg.aemeasurable
  rw [layer μ, layer μ']
  have hmeas0 : Measurable fun t : ℝ => μ' {a | t < g a} := by
    apply Antitone.measurable
    intro s t hst
    exact measure_mono fun a (ha : t < g a) => lt_of_le_of_lt hst ha
  have hmeas : Measurable fun t : ℝ => c * μ' {a | t < g a} := hmeas0.const_mul c
  calc ∫⁻ t in Set.Ioi 0, μ {a | t < g a}
      ≤ ∫⁻ t in Set.Ioi 0, (c * μ' {a | t < g a} + (Set.Iic (1 : ℝ)).indicator (fun _ => d) t) := by
        refine lintegral_mono fun t => ?_
        by_cases ht : t ≤ 1
        · rw [Set.indicator_of_mem (Set.mem_Iic.2 ht)]
          exact hE _ (measurableSet_lt measurable_const hg)
        · have : {a | t < g a} = ∅ := by
            ext a
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
            linarith [hg1 a, not_le.1 ht]
          rw [this, measure_empty]
          exact zero_le
    _ = c * (∫⁻ t in Set.Ioi 0, μ' {a | t < g a}) +
          ∫⁻ t in Set.Ioi 0, (Set.Iic (1 : ℝ)).indicator (fun _ => d) t := by
        rw [lintegral_add_left hmeas, lintegral_const_mul _ hmeas0]
    _ = c * (∫⁻ t in Set.Ioi 0, μ' {a | t < g a}) + d := by
        rw [lintegral_indicator_const measurableSet_Iic d,
          Measure.restrict_apply measurableSet_Iic, Set.inter_comm, Set.Ioi_inter_Iic,
          Real.volume_Ioc]
        simp

end SolPrivGaussMSA2

open SolPrivGaussMSA2 in
theorem solution {X Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z] {n : ℕ}
    (M : (Fin n → X) → Measure Y) (K : Kernel Y Z) [IsMarkovKernel K]
    (M₁ : (Fin n → X) → Measure Y) (M₂ : (Fin n → X) → Kernel Y Z)
    [∀ x, IsMarkovKernel (M₂ x)]
    (ε δ ε₁ δ₁ ε₂ δ₂ : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hε₁ : 0 ≤ ε₁) (hδ₁ : 0 ≤ δ₁)
    (hε₂ : 0 ≤ ε₂) (hδ₂ : 0 ≤ δ₂) :
    (PrivGaussMS.IsDPM M ε δ → PrivGaussMS.IsDPM (fun x => (M x).bind K) ε δ) ∧
    (PrivGaussMS.IsDPM M₁ ε₁ δ₁ → (∀ y, PrivGaussMS.IsDPM (fun x => M₂ x y) ε₂ δ₂) →
      PrivGaussMS.IsDPM (fun x => M₁ x ⊗ₘ M₂ x) (ε₁ + ε₂) (δ₁ + δ₂)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨hMp, hdp⟩
    have hb : ∀ x, IsProbabilityMeasure ((M x).bind K) := fun x => by
      haveI := hMp x
      constructor
      rw [Measure.bind_apply MeasurableSet.univ K.measurable.aemeasurable]
      simp
    refine ⟨hb, fun S S' hS O hO => ?_⟩
    show ((M S).bind K).real O ≤ Real.exp ε * ((M S').bind K).real O + δ
    haveI := hMp S
    haveI := hMp S'
    have hE : ∀ O', MeasurableSet O' →
        M S O' ≤ ENNReal.ofReal (Real.exp ε) * M S' O' + ENNReal.ofReal δ := fun O' hO' =>
      ennreal_of_real_ineq (M S) (M S') ε δ hδ (hdp S S' hS O' hO')
    have key : (M S).bind K O ≤
        ENNReal.ofReal (Real.exp ε) * (M S').bind K O + ENNReal.ofReal δ := by
      rw [Measure.bind_apply hO K.measurable.aemeasurable,
        Measure.bind_apply hO K.measurable.aemeasurable]
      exact dp_fun (M S) (M S') _ _ hE (fun y => K y O) (K.measurable_coe hO)
        (fun y => prob_le_one)
    simp only [measureReal_def]
    exact real_of_ennreal_ineq _ _ (Real.exp_pos ε).le hδ (measure_ne_top _ _) key
  · rintro ⟨hMp, hdp⟩ hM2
    have hb : ∀ x, IsProbabilityMeasure (M₁ x ⊗ₘ M₂ x) := fun x => by
      haveI := hMp x
      infer_instance
    refine ⟨hb, fun S S' hS E hE => ?_⟩
    show (M₁ S ⊗ₘ M₂ S).real E ≤
      Real.exp (ε₁ + ε₂) * (M₁ S' ⊗ₘ M₂ S').real E + (δ₁ + δ₂)
    haveI := hMp S
    haveI := hMp S'
    set c₁ := ENNReal.ofReal (Real.exp ε₁)
    set c₂ := ENNReal.ofReal (Real.exp ε₂)
    set d₁ := ENNReal.ofReal δ₁
    set d₂ := ENNReal.ofReal δ₂
    set g : Y → ENNReal := fun y => M₂ S' y (Prod.mk y ⁻¹' E) with hg_def
    have hgm : Measurable g := Kernel.measurable_kernel_prodMk_left hE
    have hfm : Measurable fun y => min 1 (c₂ * g y) := measurable_const.min (hgm.const_mul c₂)
    have hpt : ∀ y, M₂ S y (Prod.mk y ⁻¹' E) ≤ min 1 (c₂ * g y) + d₂ := by
      intro y
      obtain ⟨hp2, hdp2⟩ := hM2 y
      have h2 : M₂ S y (Prod.mk y ⁻¹' E) ≤ c₂ * g y + d₂ :=
        ennreal_of_real_ineq (M₂ S y) (M₂ S' y) ε₂ δ₂ hδ₂
          (hdp2 S S' hS _ (measurable_prodMk_left hE))
      have h1 : M₂ S y (Prod.mk y ⁻¹' E) ≤ 1 := prob_le_one
      rcases le_total 1 (c₂ * g y) with hc | hc
      · rw [min_eq_left hc]; exact le_trans h1 le_self_add
      · rw [min_eq_right hc]; exact h2
    have hE1 : ∀ O, MeasurableSet O → M₁ S O ≤ c₁ * M₁ S' O + d₁ := fun O hO =>
      ennreal_of_real_ineq (M₁ S) (M₁ S') ε₁ δ₁ hδ₁ (hdp S S' hS O hO)
    have key : (M₁ S ⊗ₘ M₂ S) E ≤
        ENNReal.ofReal (Real.exp (ε₁ + ε₂)) * (M₁ S' ⊗ₘ M₂ S') E +
          ENNReal.ofReal (δ₁ + δ₂) := by
      rw [Measure.compProd_apply hE, Measure.compProd_apply hE]
      calc ∫⁻ y, M₂ S y (Prod.mk y ⁻¹' E) ∂M₁ S
          ≤ ∫⁻ y, (min 1 (c₂ * g y) + d₂) ∂M₁ S := lintegral_mono hpt
        _ = ∫⁻ y, min 1 (c₂ * g y) ∂M₁ S + d₂ := by
            rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
        _ ≤ (c₁ * ∫⁻ y, min 1 (c₂ * g y) ∂M₁ S' + d₁) + d₂ := by
            gcongr
            exact dp_fun (M₁ S) (M₁ S') c₁ d₁ hE1 _ hfm (fun y => min_le_left _ _)
        _ ≤ (c₁ * (c₂ * ∫⁻ y, g y ∂M₁ S') + d₁) + d₂ := by
            gcongr
            rw [← lintegral_const_mul _ hgm]
            exact lintegral_mono fun y => min_le_right _ _
        _ = ENNReal.ofReal (Real.exp (ε₁ + ε₂)) * ∫⁻ y, g y ∂M₁ S' +
              ENNReal.ofReal (δ₁ + δ₂) := by
            rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos ε₁).le, ENNReal.ofReal_add hδ₁ hδ₂]
            ring
    simp only [measureReal_def]
    exact real_of_ennreal_ineq _ _ (Real.exp_pos _).le (add_nonneg hδ₁ hδ₂)
      (measure_ne_top _ _) key

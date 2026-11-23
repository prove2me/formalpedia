-- Prove2me | solution 1 for TailRiskTheory.Generator.lemma_B1_ii
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T03:27:01.15589+00:00
-- url     : https://prove2.me/submissions/f086db61-18c0-4ad9-924e-60a4467c9746

import Mathlib
import Definitions.Def_TailRiskTheory_Generator_Model
import Definitions.Def_StochasticOrders_Usual_UsualOrder
import Theorems.Thm_StochasticOrders_Usual_usual_order_coupling_iff_v2

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open TailRiskSharing.VaRConv (distFn IsAtomless)
open TailRiskSharing.VaRTail (IsMonotone IsTranslationInvariant IsMonetary IsLawInvariant)
open TailRiskSharing.TailConv (Linf)
open TailRiskTheory.Generator

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : IsAtomless P) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ X ∈ Linf P, ∀ Y ∈ Linf P, ∀ Xt ∈ Linf P, ∀ Yt ∈ Linf P,
      StOrder P X Y → IsPTailOf P p X Xt → IsPTailOf P p Y Yt → StOrder P Xt Yt) ∧
    (∀ X ∈ Linf P, ∀ Y ∈ Linf P, ∀ Xm ∈ Linf P, ∀ Ym ∈ Linf P,
      StOrder P X Y → IsPMixOf P p X Xm → IsPMixOf P p Y Ym → StOrder P Xm Ym) := by
  have hp1' : (0 : ℝ) < 1 - p := by linarith
  have hcompl : ∀ (Z : Ω → ℝ), Measurable Z → ∀ x, P {ω | x < Z ω} = 1 - P {ω | Z ω ≤ x} := by
    intro Z hZ x
    rw [← prob_compl_eq_one_sub (measurableSet_le hZ measurable_const)]
    congr 1
    ext ω
    simp [not_le]
  have hcompl_real : ∀ (Z : Ω → ℝ), Measurable Z → ∀ x,
      P.real {ω | x < Z ω} = 1 - distFn P Z x := by
    intro Z hZ x
    unfold distFn Measure.real
    rw [hcompl Z hZ x, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
  have cdf_anti : ∀ (X Y : Ω → ℝ), Measurable X → Measurable Y → StOrder P X Y →
      ∀ x, distFn P Y x ≤ distFn P X x := by
    intro X Y hXm hYm hXY x
    let f : ℝ → ℝ := fun t => if x < t then 1 else 0
    have hf : Monotone f := by
      intro a b hab
      simp only [f]
      split_ifs with ha hb <;> linarith
    have heq : ∀ (Z : Ω → ℝ), (fun ω => f (Z ω)) =
        ({ω | x < Z ω} : Set Ω).indicator (fun _ => (1 : ℝ)) := by
      intro Z
      ext ω
      simp only [f]
      by_cases h : x < Z ω <;> simp [h]
    have hint : ∀ (Z : Ω → ℝ), Measurable Z → Integrable (fun ω => f (Z ω)) P := by
      intro Z hZm
      rw [heq Z]
      exact (integrable_const (1 : ℝ)).indicator (measurableSet_lt measurable_const hZm)
    have hval : ∀ (Z : Ω → ℝ), Measurable Z → ∫ ω, f (Z ω) ∂P = 1 - distFn P Z x := by
      intro Z hZm
      rw [heq Z, integral_indicator (measurableSet_lt measurable_const hZm), setIntegral_const]
      simp only [Measure.real, smul_eq_mul, mul_one]
      simpa [Measure.real] using hcompl_real Z hZm x
    have hle := hXY f hf (hint X hXm) (hint Y hYm)
    rw [hval X hXm, hval Y hYm] at hle
    linarith
  have st_of_cdf : ∀ (Z W : Ω → ℝ), Measurable Z → Measurable W →
      (∀ x, distFn P W x ≤ distFn P Z x) → StOrder P Z W := by
    intro Z W hZm hWm hF
    have hUO : StochasticOrders.Usual.UsualOrder P P Z W := by
      intro x
      rw [hcompl Z hZm x, hcompl W hWm x]
      apply tsub_le_tsub_left
      exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp (hF x)
    obtain ⟨Ω'', mΩ, ρ, hρ, Zh, Wh, hZhm, hWhm, hZid, hWid, hle⟩ :=
      (StochasticOrders.Usual.usual_order_coupling_iff_v2 P P Z W hZm hWm).mp hUO
    intro f hf hfZ hfW
    have hfm : Measurable f := hf.measurable
    have e1 : ∫ ω, f (Z ω) ∂P = ∫ ω, f (Zh ω) ∂ρ := (hZid.comp hfm).integral_eq.symm
    have e2 : ∫ ω, f (W ω) ∂P = ∫ ω, f (Wh ω) ∂ρ := (hWid.comp hfm).integral_eq.symm
    have i1 : Integrable (fun ω => f (Zh ω)) ρ := ((hZid.comp hfm).integrable_iff).mpr hfZ
    have i2 : Integrable (fun ω => f (Wh ω)) ρ := ((hWid.comp hfm).integrable_iff).mpr hfW
    have hae : ∀ᵐ ω ∂ρ, Zh ω ≤ Wh ω := by
      rw [ae_iff]
      have hmeas : MeasurableSet {ω | Zh ω ≤ Wh ω} := measurableSet_le hZhm hWhm
      have := (prob_compl_eq_zero_iff hmeas).mpr hle
      simpa [Set.compl_def] using this
    rw [e1, e2]
    exact integral_mono_ae i1 i2 (hae.mono fun ω h => hf h)
  have essInf_mono : ∀ (X Y : Ω → ℝ), X ∈ Linf P → Y ∈ Linf P →
      (∀ x, distFn P Y x ≤ distFn P X x) → essInfRV P X ≤ essInfRV P Y := by
    intro X Y ⟨hXm, CX, hCX⟩ ⟨hYm, CY, hCY⟩ hF
    have hbdd : BddBelow {y : ℝ | 0 < distFn P X y} := by
      refine ⟨-CX, fun y hy => ?_⟩
      by_contra hy'
      push Not at hy'
      have hnull : P {ω | X ω ≤ y} = 0 := by
        apply measure_mono_null _ (ae_iff.mp hCX)
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        intro habs
        linarith [(abs_le.mp habs).1]
      have h0 : distFn P X y = 0 := by simp [distFn, Measure.real, hnull]
      simp only [Set.mem_setOf_eq] at hy
      linarith
    have hnullY : P {ω | CY < Y ω} = 0 := by
      apply measure_mono_null _ (ae_iff.mp hCY)
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      intro habs
      linarith [(abs_le.mp habs).2]
    have hprob1 : P {ω | Y ω ≤ CY} = 1 := by
      have hc : ({ω | Y ω ≤ CY} : Set Ω)ᶜ = {ω | CY < Y ω} := by ext ω; simp [not_le]
      exact (prob_compl_eq_zero_iff (measurableSet_le hYm measurable_const)).mp (by rw [hc]; exact hnullY)
    have hCY_pos : CY ∈ {y : ℝ | 0 < distFn P Y y} := by
      simp [distFn, Measure.real, hprob1]
    exact csInf_le_csInf hbdd ⟨CY, hCY_pos⟩ (fun x hx => lt_of_lt_of_le hx (hF x))
  constructor
  · intro X hX Y hY Xt hXt Yt hYt hXY hXXt hYYt
    have hF := cdf_anti X Y hX.1 hY.1 hXY
    apply st_of_cdf Xt Yt hXt.1 hYt.1
    intro x
    rw [hXXt x, hYYt x]
    unfold tailDistFn
    exact div_le_div_of_nonneg_right (max_le_max_right 0 (by linarith [hF x])) hp1'.le
  · intro X hX Y hY Xm hXm Ym hYm hXY hXXm hYYm
    have hF := cdf_anti X Y hX.1 hY.1 hXY
    have hess := essInf_mono X Y hX hY hF
    apply st_of_cdf Xm Ym hXm.1 hYm.1
    intro x
    rw [hXXm x, hYYm x]
    have h1 : (if essInfRV P Y ≤ x then (1 : ℝ) else 0) ≤
        (if essInfRV P X ≤ x then 1 else 0) := by
      split_ifs <;> linarith
    have h2 := hF x
    nlinarith

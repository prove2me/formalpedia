-- Prove2me | solution 1 for TailRiskSharing.VaRConv.display12_var_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:20:59.707305+00:00
-- url     : https://prove2.me/submissions/f6952c05-00f2-470f-9b6b-437619eef7b8

import Mathlib
import Definitions.Def_TailRiskSharing_VaRConv_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory TailRiskSharing.VaRConv

namespace TRCHelp
open MeasureTheory ProbabilityTheory TailRiskSharing.VaRConv

theorem distFn_eq_cdf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (x : ℝ) :
    distFn P X x = cdf (P.map X) x := by
  haveI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  rw [cdf_eq_real, distFn, Measure.real, Measure.real, Measure.map_apply hX measurableSet_Iic]
  rfl

theorem set_ne {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (c : ℝ) (hc0 : c < 1) (hc1 : 0 < c) :
    {x | c ≤ distFn P X x}.Nonempty ∧ BddBelow {x | c ≤ distFn P X x} := by
  haveI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have h1 := tendsto_cdf_atTop (P.map X)
  have h0 := tendsto_cdf_atBot (P.map X)
  constructor
  · obtain ⟨x, hx⟩ := (h1.eventually (eventually_ge_nhds hc0)).exists
    exact ⟨x, by show c ≤ distFn P X x; rw [distFn_eq_cdf P X hX]; exact hx⟩
  · have : ∀ᶠ x in Filter.atBot, cdf (P.map X) x < c := h0.eventually (eventually_lt_nhds hc1)
    obtain ⟨b, hb⟩ := Filter.eventually_atBot.mp this
    refine ⟨b, fun y hy => ?_⟩
    by_contra hlt
    push Not at hlt
    have := hb y hlt.le
    have hy' : c ≤ distFn P X y := hy
    rw [distFn_eq_cdf P X hX] at hy'
    linarith

theorem set_ne' {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (c : ℝ) (hc0 : c < 1) (hc1 : 0 < c) :
    {x | c < distFn P X x}.Nonempty ∧ BddBelow {x | c < distFn P X x} := by
  haveI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have h1 := tendsto_cdf_atTop (P.map X)
  constructor
  · obtain ⟨x, hx⟩ := (h1.eventually (eventually_gt_nhds hc0)).exists
    exact ⟨x, by show c < distFn P X x; rw [distFn_eq_cdf P X hX]; exact hx⟩
  · exact (set_ne P X hX c hc0 hc1).2.mono (fun x (hx : c < distFn P X x) => (le_of_lt hx : c ≤ distFn P X x))

theorem real_gt_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (ε : ℝ) :
    P.real {ω | ε < X ω} = 1 - distFn P X ε := by
  have : {ω | ε < X ω} = {ω | X ω ≤ ε}ᶜ := by ext ω; simp
  rw [this]
  show P.real (X ⁻¹' Set.Iic ε)ᶜ = _
  rw [probReal_compl_eq_one_sub (hX measurableSet_Iic)]
  rfl

end TRCHelp

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (α₁ : ℝ) (hα0 : 0 < α₁) (hα1 : α₁ < 1) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < α₁)
    (X : Ω → ℝ) (hX : X ∈ (L0 : Set (Ω → ℝ))) :
    VaRR P α₁ X ≤ VaRL P (α₁ - δ) X ∧ VaRL P α₁ X ≤ VaRR P α₁ X := by
  have hXm : Measurable X := hX
  constructor
  · unfold VaRR VaRL
    apply csInf_le_csInf (TRCHelp.set_ne' P X hXm (1 - α₁) (by linarith) (by linarith)).2
      (TRCHelp.set_ne P X hXm (1 - (α₁ - δ)) (by linarith) (by linarith)).1
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    linarith
  · unfold VaRR VaRL
    apply csInf_le_csInf (TRCHelp.set_ne P X hXm (1 - α₁) (by linarith) (by linarith)).2
      (TRCHelp.set_ne' P X hXm (1 - α₁) (by linarith) (by linarith)).1
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    exact hx.le

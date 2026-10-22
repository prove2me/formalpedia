-- Prove2me | solution 1 for TailRiskSharing.VaRConv.display10_11_var_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:23:07.395872+00:00
-- url     : https://prove2.me/submissions/76dd22ea-af3e-45ff-bbc8-bc3b8198df04

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
    (Y : Ω → ℝ) (hY : Y ∈ (L0 : Set (Ω → ℝ))) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    (VaRR P β Y ≤ 0 ↔ ∀ ε : ℝ, 0 < ε → P.real {ω | ε < Y ω} < β) ∧
    (VaRL P β Y ≤ 0 ↔ P.real {ω | 0 < Y ω} ≤ β) := by
  have hYm : Measurable Y := hY
  haveI : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hYm.aemeasurable
  obtain ⟨hne', hbdd'⟩ := TRCHelp.set_ne' P Y hYm (1 - β) (by linarith) (by linarith)
  obtain ⟨hne, hbdd⟩ := TRCHelp.set_ne P Y hYm (1 - β) (by linarith) (by linarith)
  constructor
  · constructor
    · intro h ε hε
      have hlt : sInf {x | 1 - β < distFn P Y x} < ε := lt_of_le_of_lt h hε
      obtain ⟨x, hx, hxε⟩ := exists_lt_of_csInf_lt hne' hlt
      have hx' : 1 - β < distFn P Y x := hx
      have hmono : distFn P Y x ≤ distFn P Y ε := by
        rw [TRCHelp.distFn_eq_cdf P Y hYm, TRCHelp.distFn_eq_cdf P Y hYm]
        exact (monotone_cdf _) hxε.le
      rw [TRCHelp.real_gt_eq P Y hYm]
      linarith
    · intro h
      apply le_of_forall_pos_le_add
      intro ε hε
      have hmem : ε ∈ {x | 1 - β < distFn P Y x} := by
        have := h ε hε
        rw [TRCHelp.real_gt_eq P Y hYm] at this
        show 1 - β < distFn P Y ε
        linarith
      have : VaRR P β Y ≤ ε := csInf_le hbdd' hmem
      linarith
  · constructor
    · intro h
      have hF : ∀ ε : ℝ, 0 < ε → 1 - β ≤ distFn P Y ε := by
        intro ε hε
        have hlt : sInf {x | 1 - β ≤ distFn P Y x} < ε := lt_of_le_of_lt h hε
        obtain ⟨x, hx, hxε⟩ := exists_lt_of_csInf_lt hne hlt
        have hx' : 1 - β ≤ distFn P Y x := hx
        have hmono : distFn P Y x ≤ distFn P Y ε := by
          rw [TRCHelp.distFn_eq_cdf P Y hYm, TRCHelp.distFn_eq_cdf P Y hYm]
          exact (monotone_cdf _) hxε.le
        linarith
      have hrc : Filter.Tendsto (cdf (P.map Y)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (cdf (P.map Y) 0)) :=
        ((cdf (P.map Y)).right_continuous 0).tendsto.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
      have h0 : 1 - β ≤ cdf (P.map Y) 0 := by
        refine ge_of_tendsto hrc ?_
        filter_upwards [self_mem_nhdsWithin] with ε hε
        have := hF ε hε
        rwa [TRCHelp.distFn_eq_cdf P Y hYm] at this
      rw [TRCHelp.real_gt_eq P Y hYm, TRCHelp.distFn_eq_cdf P Y hYm]
      linarith
    · intro h
      have hmem : (0 : ℝ) ∈ {x | 1 - β ≤ distFn P Y x} := by
        rw [TRCHelp.real_gt_eq P Y hYm] at h
        show 1 - β ≤ distFn P Y 0
        linarith
      exact csInf_le hbdd hmem

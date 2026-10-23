-- Prove2me | solution 1 for WassersteinLinOpt.Ball.tendsto_iff_limsup_quasiIntegral_le
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T05:35:28.994989+00:00
-- url     : https://prove2.me/submissions/ff2f1e27-d7bd-4dd5-a842-05918318a69e

/-
The layer-cake proof below adapts Mathlib/MeasureTheory/Measure/Portmanteau.lean.
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors of the adapted Mathlib argument: Kalle Kytölä.
-/
import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_quasiIntegral

/- Portmanteau support for Yue, Kuhn and Wiesemann, On linear optimization over
Wasserstein balls, author manuscript 7 June 2021, Appendix A, Lemma 3.
Formalization by Alexander Richard Towell (queelius), with substantial OpenAI
Codex assistance. The layer-cake argument adapts Mathlib's continuous version
in MeasureTheory.Measure.Portmanteau to lower semicontinuous functions. -/
open MeasureTheory Filter Set
open scoped ENNReal NNReal
noncomputable section
namespace PortmanteauSupport
open WassersteinLinOpt.Ball

theorem lsc_lintegral_le_liminf {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {μ : ProbabilityMeasure X} {μs : ℕ → ProbabilityMeasure X}
    (hlim : Tendsto μs atTop (nhds μ)) (f : X → ℝ)
    (hf : LowerSemicontinuous f) (hn : ∀ x, 0 ≤ f x) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂(μ : Measure X) ≤
      liminf (fun k => ∫⁻ x, ENNReal.ofReal (f x) ∂(μs k : Measure X)) atTop := by
  simp_rw [lintegral_eq_lintegral_meas_lt _ (Eventually.of_forall hn) hf.measurable.aemeasurable]
  calc
    ∫⁻ t in Ioi (0 : ℝ), (μ : Measure X) {x | t < f x} ≤
        ∫⁻ t in Ioi (0 : ℝ), liminf (fun k => (μs k : Measure X) {x | t < f x}) atTop := by
      apply lintegral_mono
      intro t
      exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim (hf.isOpen_preimage t)
    _ ≤ liminf (fun k => ∫⁻ t in Ioi (0 : ℝ), (μs k : Measure X) {x | t < f x}) atTop := by
      apply lintegral_liminf_le
      intro k
      exact Antitone.measurable (fun s t hst => measure_mono (fun x hx => lt_of_le_of_lt hst hx))

theorem quasiIntegral_shift {X : Type*} [MeasurableSpace X]
    (μ : ProbabilityMeasure X) (g : X → ℝ) (hg : Measurable g)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, g x ≤ C) :
    quasiIntegral g (μ : Measure X) = (C : EReal) -
      ((∫⁻ x, ENNReal.ofReal (C - g x) ∂(μ : Measure X) : ℝ≥0∞) : EReal) := by
  let P := ∫⁻ x, ENNReal.ofReal (g x) ∂(μ : Measure X)
  let N := ∫⁻ x, ENNReal.ofReal (-g x) ∂(μ : Measure X)
  let L := ∫⁻ x, ENNReal.ofReal (C - g x) ∂(μ : Measure X)
  have hpbound : P ≤ ENNReal.ofReal C := by
    calc P ≤ ∫⁻ _x : X, ENNReal.ofReal C ∂(μ : Measure X) :=
        lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hb x))
      _ = ENNReal.ofReal C := by simp
  have hp : P ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hpbound
  have hpoint : ∀ x, ENNReal.ofReal (g x) + ENNReal.ofReal (C - g x) =
      ENNReal.ofReal C + ENNReal.ofReal (-g x) := by
    intro x
    by_cases hx : 0 ≤ g x
    · rw [ENNReal.ofReal_of_nonpos (neg_nonpos.mpr hx), add_zero,
        ← ENNReal.ofReal_add hx (sub_nonneg.mpr (hb x))]
      congr 1 <;> ring
    · have hx' : g x ≤ 0 := le_of_not_ge hx
      rw [ENNReal.ofReal_of_nonpos hx', zero_add, ← ENNReal.ofReal_add hC (neg_nonneg.mpr hx')]
      congr 1 <;> ring
  have hadd : P + L = ENNReal.ofReal C + N := by
    change (∫⁻ x, ENNReal.ofReal (g x) ∂(μ : Measure X)) +
      (∫⁻ x, ENNReal.ofReal (C - g x) ∂(μ : Measure X)) = _
    rw [← lintegral_add_left hg.ennreal_ofReal, lintegral_congr hpoint,
      lintegral_add_left measurable_const]
    simp [N]
  change (P : EReal) - (N : EReal) = (C : EReal) - (L : EReal)
  by_cases hn : N = ⊤
  · have hl : L = ⊤ := by
      have : P + L = ⊤ := by simpa [hn] using hadd
      exact (ENNReal.add_eq_top.mp this).resolve_left hp
    simp [hn, hl]
  · have hl : L ≠ ⊤ := by
      intro hl
      have : ENNReal.ofReal C + N = ⊤ := by simpa [hl] using hadd.symm
      exact (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hn⟩) this
    have hreal := congrArg ENNReal.toReal hadd
    rw [ENNReal.toReal_add hp hl, ENNReal.toReal_add ENNReal.ofReal_ne_top hn,
      ENNReal.toReal_ofReal hC] at hreal
    rw [← EReal.coe_ennreal_toReal hp, ← EReal.coe_ennreal_toReal hn,
      ← EReal.coe_ennreal_toReal hl, ← EReal.coe_sub, ← EReal.coe_sub]
    congr 1
    linarith

theorem quasiIntegral_limsup {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {μ : ProbabilityMeasure X} {μs : ℕ → ProbabilityMeasure X}
    (hlim : Tendsto μs atTop (nhds μ)) (g : X → ℝ)
    (hb : BddAbove (Set.range g)) (hg : UpperSemicontinuous g) :
    limsup (fun k => quasiIntegral g (μs k : Measure X)) atTop ≤
      quasiIntegral g (μ : Measure X) := by
  obtain ⟨c, hc⟩ := hb
  let C : ℝ := max c 0
  have hC : 0 ≤ C := le_max_right _ _
  have hbound : ∀ x, g x ≤ C := fun x => (hc (mem_range_self x)).trans (le_max_left _ _)
  have hlsc : LowerSemicontinuous (fun x => C - g x) := by
    apply lowerSemicontinuous_iff_isOpen_preimage.mpr
    intro a
    convert hg.isOpen_preimage (C-a) using 1
    ext x
    simp only [mem_preimage, mem_Ioi, mem_Iio]
    constructor <;> intro h <;> linarith
  let L := fun (ν : ProbabilityMeasure X) => ∫⁻ x, ENNReal.ofReal (C - g x) ∂(ν : Measure X)
  have hi : L μ ≤ liminf (fun k => L (μs k)) atTop :=
    lsc_lintegral_le_liminf hlim _ hlsc (fun x => sub_nonneg.mpr (hbound x))
  have hmap := EReal.coe_ennreal_strictMono.monotone.map_liminf_of_continuousAt
    (F := atTop) (fun k => L (μs k)) continuous_coe_ennreal_ereal.continuousAt
  simp only [Function.comp_def] at hmap
  have hi' : (L μ : EReal) ≤ liminf (fun k => (L (μs k) : EReal)) atTop := by
    rw [← hmap]
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr hi
  have hneg : limsup (fun k => -(L (μs k) : EReal)) atTop ≤ -(L μ : EReal) := by
    simpa only [← Pi.neg_def, EReal.limsup_neg] using EReal.neg_le_neg_iff.mpr hi'
  have hadd := EReal.limsup_add_le (f := atTop) (u := fun _ : ℕ => (C : EReal))
    (v := fun k => -(L (μs k) : EReal)) (Or.inl (by simp)) (Or.inl (by simp))
  simp only [limsup_const] at hadd
  have h := hadd.trans (add_le_add (le_refl (C : EReal)) hneg)
  simpa only [quasiIntegral_shift _ g hg.measurable C hC hbound, sub_eq_add_neg,
    Pi.add_def, L] using h

theorem quasiIntegral_indicator {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : Set X) (hF : MeasurableSet F) :
    quasiIntegral (F.indicator (fun _ : X => (1 : ℝ))) μ = ((μ F : ℝ≥0∞) : EReal) := by
  have hp : (fun x => ENNReal.ofReal (F.indicator (fun _ : X => (1 : ℝ)) x)) =
      F.indicator (fun _ : X => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x ∈ F <;> simp [hx]
  have hn : (fun x => ENNReal.ofReal (-(F.indicator (fun _ : X => (1 : ℝ)) x))) =
      fun _ : X => (0 : ℝ≥0∞) := by
    funext x
    by_cases hx : x ∈ F <;> simp [hx]
  simp only [quasiIntegral, hp, hn, lintegral_indicator hF, lintegral_one,
    Measure.restrict_apply_univ, lintegral_zero, EReal.coe_ennreal_zero, sub_zero]

theorem tendsto_of_quasiIntegral_limsup {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (h : ∀ g : X → ℝ, BddAbove (Set.range g) → UpperSemicontinuous g →
      limsup (fun k => quasiIntegral g (μs k : Measure X)) atTop ≤
        quasiIntegral g (μ : Measure X)) : Tendsto μs atTop (nhds μ) := by
  apply tendsto_of_forall_isClosed_limsup_le'
  intro F hF
  have hb : BddAbove (Set.range (F.indicator (fun _ : X => (1 : ℝ)))) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ F <;> simp [hx]
  have hi := h (F.indicator (fun _ : X => (1 : ℝ))) hb
    (hF.upperSemicontinuous_indicator (by norm_num))
  simp only [quasiIntegral_indicator _ F hF.measurableSet] at hi
  have hmap := EReal.coe_ennreal_strictMono.monotone.map_limsup_of_continuousAt
    (F := atTop) (fun k => (μs k : Measure X) F) continuous_coe_ennreal_ereal.continuousAt
  simp only [Function.comp_def] at hmap
  rw [← hmap] at hi
  exact EReal.coe_ennreal_le_coe_ennreal_iff.mp hi

end PortmanteauSupport

theorem solution {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] (μs : ℕ → ProbabilityMeasure X)
    (μlim : ProbabilityMeasure X) :
    Filter.Tendsto μs Filter.atTop (nhds μlim) ↔
      ∀ g : X → ℝ, BddAbove (Set.range g) → UpperSemicontinuous g →
        Filter.limsup (fun k => WassersteinLinOpt.Ball.quasiIntegral g (μs k : Measure X)) Filter.atTop ≤
          WassersteinLinOpt.Ball.quasiIntegral g (μlim : Measure X) := by
  constructor
  · intro h g hb hg
    exact PortmanteauSupport.quasiIntegral_limsup h g hb hg
  · exact PortmanteauSupport.tendsto_of_quasiIntegral_limsup μs μlim

#print axioms PortmanteauSupport.lsc_lintegral_le_liminf
#print axioms PortmanteauSupport.quasiIntegral_shift
#print axioms PortmanteauSupport.quasiIntegral_limsup
#print axioms solution

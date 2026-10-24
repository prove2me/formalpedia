-- Prove2me | solution 1 for WassersteinLinOpt.Ball.optimalValue_attained
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T06:48:25.457843+00:00
-- url     : https://prove2.me/submissions/4d521639-6257-4000-82c0-bea8370f033e

/-
Attainment of linear optimization over a positive-radius Wasserstein ball under
upper semicontinuity and a strict sub-p growth bound. Original mathematics:
Yue, Kuhn and Wiesemann, On linear optimization over Wasserstein balls (2021),
Theorem 3, DOI 10.1007/s10107-021-01673-8.
Formalization: Alexander Richard Towell (queelius), substantial OpenAI Codex
assistance, 23 October 2026. New work: affine-moment envelope, extended-real
Portmanteau argument including minus infinity, and compact-subtype maximization.
Reuses actual accepted bodies from queelius: bounded Portmanteau submission
ff2f1e27-d7bd-4dd5-a842-05918318a69e (4dad192cb74805942e9fd91864fb0af1efce3b87226886cbc9027c3f47c18ba7),
and compactness submission d0813959-fe0d-4302-8a4e-a745ca8d49d8
(c35c6727f47ea7d9f5f63beac946d4984be3a5d2e8e600e281c1bed73c182a2f),
including its uniform-moment and tightness proofs. Original notices retained.
This establishes the exact platform statement; no novelty or human review claim.
-/
/-
The layer-cake proof below adapts Mathlib/MeasureTheory/Measure/Portmanteau.lean.
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors of the adapted Mathlib argument: Kalle Kytölä.
-/
import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_quasiIntegral
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinBall
import Definitions.Def_WassersteinLinOpt_Ball_HasFinitePthMoment
import Definitions.Def_WassersteinLinOpt_Ball_optimalValue

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

theorem bounded_portmanteau {X : Type*} [MetricSpace X] [ProperSpace X]
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
#print axioms bounded_portmanteau

/- Moment-controlled extension of Portmanteau, 23 October2026.
The accepted bounded Portmanteau proof above is retained with its top theorem
renamed; SHA2564dad192cb74805942e9fd91864fb0af1efce3b87226886cbc9027c3f47c18ba7.
Original setting: Yue, Kuhn and Wiesemann, Theorem3 and AppendixA.
Alexander Richard Towell directed the work; OpenAI Codex constructed this
extension. No novelty or independent human review is asserted. -/
namespace MomentPortmanteau
open WassersteinLinOpt.Ball

theorem quasiIntegral_majorant {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f h : X → ℝ) (hf : Measurable f) (hh : Measurable h)
    (hh0 : ∀ x, 0 ≤ h x) (hfh : ∀ x, f x ≤ h x)
    (hhfin : ∫⁻ x, ENNReal.ofReal (h x) ∂μ ≠ ⊤) :
    quasiIntegral f μ =
      ((∫⁻ x, ENNReal.ofReal (h x) ∂μ : ℝ≥0∞) : EReal) -
      ((∫⁻ x, ENNReal.ofReal (h x - f x) ∂μ : ℝ≥0∞) : EReal) := by
  let P := ∫⁻ x, ENNReal.ofReal (f x) ∂μ
  let N := ∫⁻ x, ENNReal.ofReal (-f x) ∂μ
  let H := ∫⁻ x, ENNReal.ofReal (h x) ∂μ
  let L := ∫⁻ x, ENNReal.ofReal (h x - f x) ∂μ
  have hp : P ≠ ⊤ := ne_top_of_le_ne_top hhfin
    (lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hfh x)))
  have hpoint : ∀ x, ENNReal.ofReal (f x) + ENNReal.ofReal (h x-f x) =
      ENNReal.ofReal (h x) + ENNReal.ofReal (-f x) := by
    intro x
    by_cases hx : 0 ≤ f x
    · rw [ENNReal.ofReal_of_nonpos (neg_nonpos.mpr hx),add_zero,
        ← ENNReal.ofReal_add hx (sub_nonneg.mpr (hfh x))]
      congr 1 <;> ring
    · have hx' : f x ≤ 0 := le_of_not_ge hx
      rw [ENNReal.ofReal_of_nonpos hx',zero_add,
        ← ENNReal.ofReal_add (hh0 x) (neg_nonneg.mpr hx')]
      congr 1 <;> ring
  have hadd : P + L = H + N := by
    change (∫⁻ x, ENNReal.ofReal (f x) ∂μ) + (∫⁻ x, ENNReal.ofReal (h x-f x) ∂μ) = _
    rw [← lintegral_add_left hf.ennreal_ofReal,lintegral_congr hpoint,
      lintegral_add_left hh.ennreal_ofReal]
  change (P : EReal) - (N : EReal) = (H : EReal) - (L : EReal)
  by_cases hn : N = ⊤
  · have hl : L = ⊤ := by
      have : P+L = ⊤ := by simpa [hn] using hadd
      exact (ENNReal.add_eq_top.mp this).resolve_left hp
    simp [hn,hl]
  · have hl : L ≠ ⊤ := by
      intro hl
      have : H+N = ⊤ := by simpa [hl] using hadd.symm
      exact (ENNReal.add_ne_top.mpr ⟨hhfin,hn⟩) this
    have hreal := congrArg ENNReal.toReal hadd
    rw [ENNReal.toReal_add hp hl,ENNReal.toReal_add hhfin hn] at hreal
    rw [← EReal.coe_ennreal_toReal hp,← EReal.coe_ennreal_toReal hn,
      ← EReal.coe_ennreal_toReal hhfin,← EReal.coe_ennreal_toReal hl,
      ← EReal.coe_sub,← EReal.coe_sub]
    congr 1
    linarith


theorem majorant_limsup {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : ProbabilityMeasure X} {μs : ℕ → ProbabilityMeasure X}
    (hlim : Tendsto μs atTop (nhds μ)) (f h : X → ℝ)
    (hf : Measurable f) (hh : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    (hfh : ∀ x, f x ≤ h x) (hlsc : LowerSemicontinuous (fun x => h x-f x))
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ k, ∫⁻ x, ENNReal.ofReal (h x) ∂(μs k : Measure X) ≤ ENNReal.ofReal C) :
    limsup (fun k => quasiIntegral f (μs k : Measure X)) atTop ≤
      (C : EReal) - ((∫⁻ x, ENNReal.ofReal (h x-f x) ∂(μ : Measure X) : ℝ≥0∞) : EReal) := by
  let L := fun ν : ProbabilityMeasure X => ∫⁻ x, ENNReal.ofReal (h x-f x) ∂(ν : Measure X)
  have hi := PortmanteauSupport.lsc_lintegral_le_liminf hlim (fun x => h x-f x)
    hlsc (fun x => sub_nonneg.mpr (hfh x))
  have hmap := EReal.coe_ennreal_strictMono.monotone.map_liminf_of_continuousAt
    (F := atTop) (fun k => L (μs k)) continuous_coe_ennreal_ereal.continuousAt
  simp only [Function.comp_def] at hmap
  have hi' : (L μ : EReal) ≤ liminf (fun k => (L (μs k) : EReal)) atTop := by
    rw [← hmap]
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr hi
  have hn : limsup (fun k => -(L (μs k) : EReal)) atTop ≤ -(L μ : EReal) := by
    simpa only [← Pi.neg_def,EReal.limsup_neg] using EReal.neg_le_neg_iff.mpr hi'
  have hadd := EReal.limsup_add_le (f := atTop) (u := fun _ : ℕ => (C : EReal))
    (v := fun k => -(L (μs k) : EReal)) (Or.inl (by simp)) (Or.inl (by simp))
  simp only [limsup_const] at hadd
  have hupper : limsup (fun k => (C : EReal) - (L (μs k) : EReal)) atTop ≤
      (C : EReal) - (L μ : EReal) := by
    simpa only [sub_eq_add_neg,Pi.add_def] using hadd.trans (add_le_add le_rfl hn)
  apply le_trans (limsup_le_limsup (Eventually.of_forall (fun k => ?_))) hupper
  rw [quasiIntegral_majorant (μs k : Measure X) f h hf hh hh0 hfh
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hb k))]
  apply EReal.sub_le_sub _ le_rfl
  have hc := EReal.coe_ennreal_le_coe_ennreal_iff.mpr (hb k)
  simpa [EReal.coe_ennreal_ofReal,hC] using hc


theorem subpower_majorant (c p q ε : ℝ) (hc : 0 < c) (hq : 0 < q)
    (hqp : q < p) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → c * (1+t^q) ≤ C + ε*t^p := by
  have hlim : Tendsto (fun t : ℝ => 2*c*t^(-(p-q))) atTop (nhds 0) := by
    simpa using (tendsto_rpow_neg_atTop (sub_pos.mpr hqp)).const_mul (2*c)
  have he : ∀ᶠ t : ℝ in atTop, 2*c*t^(-(p-q)) < ε := hlim.eventually (gt_mem_nhds hε)
  obtain ⟨R,hR⟩ := eventually_atTop.mp he
  let R' : ℝ := max 1 R
  let C : ℝ := c*(1+R'^q)
  have hR' : 1 ≤ R' := le_max_left _ _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro t ht
  by_cases hsmall : t ≤ R'
  · have hpow := Real.rpow_le_rpow ht hsmall hq.le
    have hp0 := mul_nonneg hε.le (Real.rpow_nonneg ht p)
    dsimp [C]
    nlinarith
  · have htR : R' ≤ t := le_of_not_ge hsmall
    have ht1 : 1 ≤ t := hR'.trans htR
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
    have hbound := (hR t ((le_max_right 1 R).trans htR)).le
    have hpow1 : 1 ≤ t^q := Real.one_le_rpow ht1 hq.le
    have hid : t^q = t^(-(p-q)) * t^p := by
      rw [← Real.rpow_add htpos]
      congr 1
      ring
    calc
      c*(1+t^q) ≤ 2*c*t^q := by nlinarith
      _ = (2*c*t^(-(p-q))) * t^p := by rw [hid]; ring
      _ ≤ ε*t^p := mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg ht p)
      _ ≤ C+ε*t^p := by linarith


theorem affine_lintegral {X : Type*} [MeasurableSpace X]
    (μ : ProbabilityMeasure X) (V : X → ℝ) (hV : Measurable V) (hV0 : ∀ x, 0 ≤ V x)
    (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 ≤ ε) :
    (∫⁻ x, ENNReal.ofReal (C+ε*V x) ∂(μ : Measure X)) =
      ENNReal.ofReal C + ENNReal.ofReal ε * ∫⁻ x, ENNReal.ofReal (V x) ∂(μ : Measure X) := by
  simp_rw [ENNReal.ofReal_add hC (mul_nonneg hε (hV0 _)),ENNReal.ofReal_mul hε]
  rw [lintegral_add_left measurable_const,lintegral_const_mul _ hV.ennreal_ofReal]
  simp

theorem moment_limsup {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : ProbabilityMeasure X} {μs : ℕ → ProbabilityMeasure X}
    (hlim : Tendsto μs atTop (nhds μ)) (f V : X → ℝ)
    (hf : UpperSemicontinuous f) (hV : Continuous V) (hV0 : ∀ x, 0 ≤ V x)
    (M : ℝ) (hM : 0 < M)
    (hm : ∫⁻ x, ENNReal.ofReal (V x) ∂(μ : Measure X) ≤ ENNReal.ofReal M)
    (hms : ∀ k, ∫⁻ x, ENNReal.ofReal (V x) ∂(μs k : Measure X) ≤ ENNReal.ofReal M)
    (hgrowth : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ x, f x ≤ C+ε*V x) :
    limsup (fun k => quasiIntegral f (μs k : Measure X)) atTop ≤ quasiIntegral f (μ : Measure X) := by
  have heps : ∀ ε : ℝ, 0 < ε →
      limsup (fun k => quasiIntegral f (μs k : Measure X)) atTop ≤
        quasiIntegral f (μ : Measure X) + ((ε*M : ℝ) : EReal) := by
    intro ε hε
    obtain ⟨C,hC,hdom⟩ := hgrowth ε hε
    let H : X → ℝ := fun x => C+ε*V x
    have hH : Continuous H := by dsimp [H]; fun_prop
    have hH0 : ∀ x, 0 ≤ H x := fun x => add_nonneg hC (mul_nonneg hε.le (hV0 x))
    have hbound : ∀ ν : ProbabilityMeasure X,
        (∫⁻ x, ENNReal.ofReal (V x) ∂(ν : Measure X) ≤ ENNReal.ofReal M) →
        ∫⁻ x, ENNReal.ofReal (H x) ∂(ν : Measure X) ≤ ENNReal.ofReal (C+ε*M) := by
      intro ν hν
      rw [affine_lintegral ν V hV.measurable hV0 C ε hC hε.le,
        ENNReal.ofReal_add hC (mul_nonneg hε.le hM.le),ENNReal.ofReal_mul hε.le]
      gcongr
    have hn : LowerSemicontinuous (fun x => -f x) :=
      continuous_neg.comp_upperSemicontinuous_antitone hf (fun _ _ h => neg_le_neg h)
    have hHf : LowerSemicontinuous (fun x => H x-f x) := by
      simpa [sub_eq_add_neg] using hH.lowerSemicontinuous.add hn
    have hupper := majorant_limsup hlim f H hf.measurable hH.measurable hH0 hdom hHf
      (C+ε*M) (add_nonneg hC (mul_nonneg hε.le hM.le)) (fun k => hbound (μs k) (hms k))
    have hfin : ∫⁻ x, ENNReal.ofReal (H x) ∂(μ : Measure X) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound μ hm)
    have hlo : ENNReal.ofReal C ≤ ∫⁻ x, ENNReal.ofReal (H x) ∂(μ : Measure X) := by
      rw [affine_lintegral μ V hV.measurable hV0 C ε hC hε.le]
      exact le_add_right le_rfl
    have hlo' : (C : EReal) ≤ ((∫⁻ x, ENNReal.ofReal (H x) ∂(μ : Measure X) : ℝ≥0∞) : EReal) := by
      have hh := EReal.coe_ennreal_le_coe_ennreal_iff.mpr hlo
      simpa [EReal.coe_ennreal_ofReal,hC] using hh
    apply hupper.trans
    rw [quasiIntegral_majorant (μ : Measure X) f H hf.measurable hH.measurable hH0 hdom hfin]
    rw [EReal.coe_add]
    calc
      _ ≤ (((∫⁻ x, ENNReal.ofReal (H x) ∂(μ : Measure X) : ℝ≥0∞) : EReal) + (ε*M : ℝ)) -
          ((∫⁻ x, ENNReal.ofReal (H x-f x) ∂(μ : Measure X) : ℝ≥0∞) : EReal) :=
        EReal.sub_le_sub (add_le_add hlo' le_rfl) le_rfl
      _ = _ := by simp only [sub_eq_add_neg]; ac_rfl
  generalize hval : quasiIntegral f (μ : Measure X) = v at heps ⊢
  induction v using EReal.rec with
  | bot => simpa using heps 1 zero_lt_one
  | top => exact le_top
  | coe b =>
    apply EReal.le_of_forall_lt_iff_le.mp
    intro z hz
    have hz' : b < z := EReal.coe_lt_coe_iff.mp hz
    have hh := heps ((z-b)/M) (div_pos (sub_pos.mpr hz') hM)
    have he : b + ((z-b)/M)*M = z := by field_simp [ne_of_gt hM]; ring
    simpa only [← EReal.coe_add,he] using hh


theorem subpower_limsup {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : ProbabilityMeasure X} {μs : ℕ → ProbabilityMeasure X}
    (hlim : Tendsto μs atTop (nhds μ)) (f : X → ℝ) (hf : UpperSemicontinuous f)
    (x₀ : X) (c p q M : ℝ) (hc : 0 < c) (hq : 0 < q) (hqp : q < p) (hM : 0 < M)
    (hm : ∫⁻ x, ENNReal.ofReal (dist x x₀ ^ p) ∂(μ : Measure X) ≤ ENNReal.ofReal M)
    (hms : ∀ k, ∫⁻ x, ENNReal.ofReal (dist x x₀ ^ p) ∂(μs k : Measure X) ≤ ENNReal.ofReal M)
    (hgrowth : ∀ x, f x ≤ c*(1+dist x x₀ ^ q)) :
    limsup (fun k => quasiIntegral f (μs k : Measure X)) atTop ≤ quasiIntegral f (μ : Measure X) := by
  have hp : 0 ≤ p := (lt_trans hq hqp).le
  apply moment_limsup hlim f (fun x => dist x x₀ ^ p) hf
    ((continuous_id.dist continuous_const).rpow_const (fun _ => Or.inr hp))
    (fun x => Real.rpow_nonneg dist_nonneg _) M hM hm hms
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := subpower_majorant c p q ε hc hq hqp hε
  exact ⟨C,hC,fun x => (hgrowth x).trans (hbound _ dist_nonneg)⟩

end MomentPortmanteau
#print axioms MomentPortmanteau.quasiIntegral_majorant

namespace AcceptedCompactness
/-
Weak compactness of Wasserstein balls, 23 October 2026.
Original result: Man-Chung Yue, Daniel Kuhn and Wolfram Wiesemann,
On linear optimization over Wasserstein balls, Theorem 1 (published p.1109),
author PDF 7 June 2021, https://manchungyue.com/wasserstein.pdf,
SHA256 d18b8b4c5811c379c9d0e20d444e61047dcfdcdb5b64c4f8b633ab974cbac337.
Platform formalization and definitions: mikedeng1.
This proof reuses the complete accepted uniform-moment proof (target
b635b1fe-a523-4227-b1b0-c24822a18ac5, submission
41df0545-36dd-4037-a1ad-ae66eb396df8, source SHA256
a1f41ce698e93f9c8417baca1cefd8db3660ef72064d54bb7afaefa8ba7d884f)
and the locally verified tightness/compact-closure proof from this campaign.
The new argument proves compactness of fixed-marginal couplings, lower
semicontinuity and attainment of transport cost, and represents the ball as the
continuous projection of a compact constrained coupling set. Lean/Mathlib
supply Prokhorov, Portmanteau, probability-measure topology and foundations.
Alexander Richard Towell directed the research and verification standards;
OpenAI Codex constructed and formally checked the proof. No mathematical
novelty or independent human proof review is claimed. Statement approval is
not proof review. The retained uniform-moment attribution follows.
-/
/-
Uniform moment bound on Wasserstein balls, 23 October 2026.
Original mathematics: Man-Chung Yue, Daniel Kuhn and Wolfram Wiesemann,
On linear optimization over Wasserstein balls, Lemma 1, author PDF 7 June 2021,
pp.2–3; published Math. Program. 195 (2022), pp.1107–1122.
mikedeng1 supplied the platform definitions and formal target. Shuze Chen's
statement approval is not review of this proof. No prior platform proof is used.
Alexander Richard Towell directed the campaign and verification standards;
OpenAI Codex constructed this proof and performed the formal checks.
The argument uses the coarse power triangle estimate and an approximately
minimizing coupling, without existence of an optimal coupling or a separate
Wasserstein triangle theorem. Lean/Mathlib supply measure and extended-real
foundations. No mathematical novelty or independent human review is claimed.
-/


namespace ReusedTightness

namespace ReusedUniformMoment

open MeasureTheory
open scoped ENNReal NNReal

namespace WassersteinMomentProof

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

noncomputable def cost (p : ℝ) (x y : X) : ℝ≥0∞ := ENNReal.ofReal (dist x y) ^ p
noncomputable def moment (p : ℝ) (μ : Measure X) (y : X) : ℝ≥0∞ :=
  ∫⁻ x, cost p x y ∂μ

lemma cost_measurable (p : ℝ) (y : X) : Measurable (fun x : X => cost p x y) := by
  unfold cost
  fun_prop

omit [MeasurableSpace X] [BorelSpace X] in
lemma cost_triangle (p : ℝ) (hp : 0 ≤ p) (x y z : X) :
    cost p x z ≤ (2 : ℝ≥0∞)^p * (cost p x y + cost p y z) := by
  unfold cost
  calc
    ENNReal.ofReal (dist x z) ^ p ≤
        (ENNReal.ofReal (dist x y) + ENNReal.ofReal (dist y z)) ^ p := by
      apply ENNReal.rpow_le_rpow _ hp
      rw [← ENNReal.ofReal_add dist_nonneg dist_nonneg]
      exact ENNReal.ofReal_le_ofReal (dist_triangle x y z)
    _ ≤ _ := ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow _ _ hp

lemma moment_change (p : ℝ) (hp : 0 ≤ p) (μ : ProbabilityMeasure X) (y z : X) :
    moment p (μ : Measure X) z ≤ (2 : ℝ≥0∞)^p *
      (moment p (μ : Measure X) y + cost p y z) := by
  calc
    moment p (μ : Measure X) z ≤ ∫⁻ x, (2 : ℝ≥0∞)^p *
        (cost p x y + cost p y z) ∂(μ : Measure X) :=
      lintegral_mono fun x => cost_triangle p hp x y z
    _ = _ := by
      rw [lintegral_const_mul _ (show Measurable (fun x : X => cost p x y + cost p y z) from (cost_measurable p y).add measurable_const),
        lintegral_add_left (cost_measurable p y)]
      simp [moment]

lemma coupling_bound [SecondCountableTopology X] (p : ℝ) (hp : 0 ≤ p)
    (μ ν : ProbabilityMeasure X) (γ : Measure (X × X))
    (hγ : γ ∈ WassersteinLinOpt.Ball.couplings (μ : Measure X) (ν : Measure X))
    (z : X) :
    moment p (μ : Measure X) z ≤ (2 : ℝ≥0∞)^p *
      ((∫⁻ q : X × X, cost p q.1 q.2 ∂γ) + moment p (ν : Measure X) z) := by
  have hc : Measurable (fun q : X × X => cost p q.1 q.2) := by
    unfold cost
    fun_prop
  have hfst : moment p (μ : Measure X) z = ∫⁻ q : X × X, cost p q.1 z ∂γ := by
    rw [moment, ← hγ.1, lintegral_map (cost_measurable p z) measurable_fst]
  have hsnd : moment p (ν : Measure X) z = ∫⁻ q : X × X, cost p q.2 z ∂γ := by
    rw [moment, ← hγ.2, lintegral_map (cost_measurable p z) measurable_snd]
  rw [hfst, hsnd]
  calc
    (∫⁻ q : X × X, cost p q.1 z ∂γ) ≤
        ∫⁻ q : X × X, (2 : ℝ≥0∞)^p * (cost p q.1 q.2 + cost p q.2 z) ∂γ :=
      lintegral_mono fun q => cost_triangle p hp q.1 q.2 z
    _ = _ := by
      rw [lintegral_const_mul _ (show Measurable (fun q : X × X => cost p q.1 q.2 + cost p q.2 z) from hc.add ((cost_measurable p z).comp measurable_snd)),
        lintegral_add_left hc]

end WassersteinMomentProof

open WassersteinMomentProof WassersteinLinOpt.Ball

theorem solution {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] (p r : ℝ) (hp : 1 ≤ p) (hr : 0 < r)
    (ν : ProbabilityMeasure X) (hν : HasFinitePthMoment p (ν : Measure X)) (x₀ : X) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ ∈ wassersteinBall p r ν,
      ∫⁻ x, ENNReal.ofReal (dist x x₀ ^ p) ∂(μ : Measure X) ≤ ENNReal.ofReal C := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hK : (2 : ℝ≥0∞)^p ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg hp0 (by norm_num)).ne
  obtain ⟨y, hy⟩ := hν
  have hy' : moment p (ν : Measure X) y < ⊤ := by
    simpa only [moment, cost, ENNReal.ofReal_rpow_of_nonneg dist_nonneg hp0] using hy
  have hcost : cost p y x₀ ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg hp0 ENNReal.ofReal_ne_top).ne
  have hN : moment p (ν : Measure X) x₀ ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (moment_change p hp0 ν y x₀)
    exact ENNReal.mul_ne_top hK (ENNReal.add_ne_top.mpr ⟨hy'.ne, hcost⟩)
  let R : ℝ≥0∞ := (ENNReal.ofReal r)^p + 1
  have hrpow : (ENNReal.ofReal r)^p ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg hp0 ENNReal.ofReal_ne_top).ne
  have hR : R ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hrpow, by norm_num⟩
  let B : ℝ≥0∞ := (2 : ℝ≥0∞)^p * (R + moment p (ν : Measure X) x₀)
  have hB : B ≠ ⊤ := ENNReal.mul_ne_top hK (ENNReal.add_ne_top.mpr ⟨hR, hN⟩)
  refine ⟨B.toReal + 1, by positivity, ?_⟩
  intro μ hμ
  have hw : (⨅ γ ∈ couplings (μ : Measure X) (ν : Measure X),
      ∫⁻ q : X × X, cost p q.1 q.2 ∂γ) ^ (1 / p) ≤ ENNReal.ofReal r := by
    simpa only [wassersteinBall, Set.mem_ofPred_eq, wassersteinDist, cost,
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg hp0] using hμ
  have hinf : (⨅ γ ∈ couplings (μ : Measure X) (ν : Measure X),
      ∫⁻ q : X × X, cost p q.1 q.2 ∂γ) ≤ (ENNReal.ofReal r)^p := by
    exact (ENNReal.rpow_inv_le_iff hp_pos).mp (by simpa only [one_div] using hw)
  have hlt : (⨅ γ ∈ couplings (μ : Measure X) (ν : Measure X),
      ∫⁻ q : X × X, cost p q.1 q.2 ∂γ) < R :=
    lt_of_le_of_lt hinf (ENNReal.lt_add_right hrpow (by norm_num))
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.mp hlt
  obtain ⟨hγmem, hγcost⟩ := iInf_lt_iff.mp hγ
  have hmoment : moment p (μ : Measure X) x₀ ≤ B := by
    apply (coupling_bound p hp0 μ ν γ hγmem x₀).trans
    dsimp [B]
    gcongr
  have hBreal : B ≤ ENNReal.ofReal (B.toReal + 1) := by
    calc
      B = ENNReal.ofReal B.toReal := (ENNReal.ofReal_toReal hB).symm
      _ ≤ ENNReal.ofReal (B.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)
  simpa only [moment, cost, ENNReal.ofReal_rpow_of_nonneg dist_nonneg hp0]
    using hmoment.trans hBreal

#print axioms solution

end ReusedUniformMoment

/- Uniform moment bounds imply tightness and compact closure. This is a local
support theorem, not a proof that the Wasserstein ball itself is closed.
Reuses the accepted uniform moment proof above with its attribution retained. -/
open MeasureTheory
open scoped ENNReal NNReal
open WassersteinLinOpt.Ball

namespace WassersteinTightness

lemma tight_of_uniform_moment {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] (S : Set (ProbabilityMeasure X))
    (x₀ : X) (p C : ℝ) (hp : 1 ≤ p) (hC : 0 < C)
    (hbound : ∀ μ ∈ S,
      ∫⁻ x, ENNReal.ofReal (dist x x₀ ^ p) ∂(μ : Measure X) ≤ ENNReal.ofReal C) :
    IsTightMeasureSet {((μ : ProbabilityMeasure X) : Measure X) | μ ∈ S} := by
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro ε hε
  by_cases htop : ε = ⊤
  · subst ε
    exact ⟨∅, isCompact_empty, by simp⟩
  have he : 0 < ε.toReal := ENNReal.toReal_pos (ne_of_gt hε) htop
  let R : ℝ := C / ε.toReal + 1
  have hRone : 1 ≤ R := by
    dsimp [R]
    have := div_nonneg hC.le he.le
    linarith
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hRone
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  refine ⟨Metric.closedBall x₀ R, isCompact_closedBall x₀ R, ?_⟩
  rintro _ ⟨μ, hμ, rfl⟩
  have hsub : (Metric.closedBall x₀ R)ᶜ ⊆
      {x | ENNReal.ofReal R ≤ ENNReal.ofReal (dist x x₀ ^ p)} := by
    intro x hx
    have hxR : R < dist x x₀ := by simpa only [Set.mem_compl_iff,
      Metric.mem_closedBall, not_le] using hx
    have hxone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (dist x x₀) := by
      exact_mod_cast (ENNReal.ofReal_le_ofReal (hRone.trans hxR.le))
    change ENNReal.ofReal R ≤ ENNReal.ofReal (dist x x₀ ^ p)
    rw [← ENNReal.ofReal_rpow_of_nonneg dist_nonneg hp0]
    exact (ENNReal.ofReal_le_ofReal hxR.le).trans
      (ENNReal.le_rpow_self_of_one_le hxone hp)
  have hmeas : Measurable (fun x : X => ENNReal.ofReal (dist x x₀ ^ p)) := by
    simp_rw [← ENNReal.ofReal_rpow_of_nonneg dist_nonneg hp0]
    fun_prop
  have hratio : C / R ≤ ε.toReal := by
    apply (div_le_iff₀ hR).mpr
    dsimp [R]
    field_simp
    nlinarith
  calc
    (μ : Measure X) (Metric.closedBall x₀ R)ᶜ ≤
        (μ : Measure X) {x | ENNReal.ofReal R ≤ ENNReal.ofReal (dist x x₀ ^ p)} :=
      measure_mono hsub
    _ ≤ (∫⁻ x, ENNReal.ofReal (dist x x₀ ^ p) ∂(μ : Measure X)) /
        ENNReal.ofReal R := meas_ge_le_lintegral_div hmeas.aemeasurable
          (by simpa using hR) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C / ENNReal.ofReal R := by gcongr; exact hbound μ hμ
    _ = ENNReal.ofReal (C / R) := (ENNReal.ofReal_div_of_pos hR).symm
    _ ≤ ENNReal.ofReal ε.toReal := ENNReal.ofReal_le_ofReal hratio
    _ = ε := ENNReal.ofReal_toReal htop

end WassersteinTightness

theorem solution {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] (p r : ℝ) (hp : 1 ≤ p) (hr : 0 < r)
    (ν : ProbabilityMeasure X) (hν : HasFinitePthMoment p (ν : Measure X)) :
    IsTightMeasureSet {((μ : ProbabilityMeasure X) : Measure X) |
      μ ∈ wassersteinBall p r ν} ∧ IsCompact (closure (wassersteinBall p r ν)) := by
  obtain ⟨x₀, hx₀⟩ := hν
  have hν' : HasFinitePthMoment p (ν : Measure X) := ⟨x₀, hx₀⟩
  obtain ⟨C, hC, hbound⟩ := ReusedUniformMoment.solution p r hp hr ν hν' x₀
  have ht := WassersteinTightness.tight_of_uniform_moment
    (wassersteinBall p r ν) x₀ p C hp hC hbound
  exact ⟨ht, isCompact_closure_of_isTightMeasureSet ht⟩

#print axioms solution

end ReusedTightness

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal Topology
open WassersteinLinOpt.Ball
set_option autoImplicit false

namespace CouplingResearch

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

noncomputable def first (γ : ProbabilityMeasure (X × X)) : ProbabilityMeasure X :=
  γ.map measurable_fst.aemeasurable

noncomputable def second (γ : ProbabilityMeasure (X × X)) : ProbabilityMeasure X :=
  γ.map measurable_snd.aemeasurable

lemma first_continuous : Continuous (first (X := X)) :=
  ProbabilityMeasure.continuous_map continuous_fst

lemma second_continuous : Continuous (second (X := X)) :=
  ProbabilityMeasure.continuous_map continuous_snd

lemma coupling_iff (γ : ProbabilityMeasure (X × X)) (μ ν : ProbabilityMeasure X) :
    (γ : Measure (X × X)) ∈ couplings (μ : Measure X) (ν : Measure X) ↔
      first γ = μ ∧ second γ = ν := by
  constructor
  · intro h
    exact ⟨ProbabilityMeasure.toMeasure_injective h.1,
      ProbabilityMeasure.toMeasure_injective h.2⟩
  · rintro ⟨h1,h2⟩
    exact ⟨congrArg (fun x : ProbabilityMeasure X => (x : Measure X)) h1,
      congrArg (fun x : ProbabilityMeasure X => (x : Measure X)) h2⟩

lemma couplings_closed (μ ν : ProbabilityMeasure X) :
    IsClosed {γ : ProbabilityMeasure (X × X) |
      (γ : Measure (X × X)) ∈ couplings (μ : Measure X) (ν : Measure X)} := by
  simp only [coupling_iff]
  exact (isClosed_eq first_continuous continuous_const).inter
    (isClosed_eq second_continuous continuous_const)

lemma joint_tight (S : Set (ProbabilityMeasure (X × X)))
    (h1 : IsTightMeasureSet ((fun γ => ((first γ : ProbabilityMeasure X) : Measure X)) '' S))
    (h2 : IsTightMeasureSet ((fun γ => ((second γ : ProbabilityMeasure X) : Measure X)) '' S)) :
    IsTightMeasureSet ((fun γ : ProbabilityMeasure (X × X) => (γ : Measure (X × X))) '' S) := by
  apply IsTightMeasureSet.prodMk
  · convert h1 using 1
    simp only [image_image]
    rfl
  · convert h2 using 1
    simp only [image_image]
    rfl

lemma couplings_compact [ProperSpace X] (μ ν : ProbabilityMeasure X) :
    IsCompact {γ : ProbabilityMeasure (X × X) |
      (γ : Measure (X × X)) ∈ couplings (μ : Measure X) (ν : Measure X)} := by
  let S : Set (ProbabilityMeasure (X × X)) :=
    {γ | (γ : Measure (X × X)) ∈ couplings (μ : Measure X) (ν : Measure X)}
  have ht : IsTightMeasureSet ((fun γ : ProbabilityMeasure (X × X) =>
      (γ : Measure (X × X))) '' S) := by
    apply joint_tight
    · apply (isTightMeasureSet_singleton (μ := (μ : Measure X))).subset
      rintro m ⟨γ,hγ,rfl⟩
      simp only [mem_singleton_iff]
      exact hγ.1
    · apply (isTightMeasureSet_singleton (μ := (ν : Measure X))).subset
      rintro m ⟨γ,hγ,rfl⟩
      simp only [mem_singleton_iff]
      exact hγ.2
  have hs : IsClosed S := couplings_closed μ ν
  simpa only [hs.closure_eq] using isCompact_closure_of_isTightMeasureSet ht

lemma integral_sublevel_closed [SeparableSpace X] (f : X → ℝ) (hf : Continuous f)
    (hfn : ∀ x, 0 ≤ f x) (C : ℝ≥0∞) :
    IsClosed {μ : ProbabilityMeasure X | ∫⁻ x, ENNReal.ofReal (f x) ∂(μ : Measure X) ≤ C} := by
  apply IsSeqClosed.isClosed
  intro μs μ hμs hlim
  have hi := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    hf hfn (fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG)
  exact hi.trans (liminf_le_of_frequently_le (Filter.Eventually.of_forall hμs).frequently)

end CouplingResearch

#print axioms CouplingResearch.couplings_compact
#print axioms CouplingResearch.integral_sublevel_closed

namespace CouplingResearch

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

noncomputable def transportCost (p : ℝ) (γ : ProbabilityMeasure (X × X)) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ p) ∂(γ : Measure (X × X))

lemma transportCost_lsc [SeparableSpace X] (p : ℝ) (hp : 0 ≤ p) :
    LowerSemicontinuous (transportCost (X := X) p) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro C
  exact integral_sublevel_closed (fun z : X × X => dist z.1 z.2 ^ p)
    ((continuous_fst.dist continuous_snd).rpow_const (fun _ => Or.inr hp))
    (fun _ => Real.rpow_nonneg dist_nonneg _) C

lemma exists_coupling_cost_le [ProperSpace X] (p : ℝ) (hp : 0 ≤ p)
    (μ ν : ProbabilityMeasure X) (C : ℝ≥0∞)
    (hC : (⨅ κ ∈ couplings (μ : Measure X) (ν : Measure X),
      ∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ p) ∂κ) ≤ C) :
    ∃ γ : ProbabilityMeasure (X × X),
      (γ : Measure (X × X)) ∈ couplings (μ : Measure X) (ν : Measure X) ∧
      transportCost p γ ≤ C := by
  let S : Set (ProbabilityMeasure (X × X)) :=
    {γ | (γ : Measure (X × X)) ∈ couplings (μ : Measure X) (ν : Measure X)}
  have hne : S.Nonempty := by
    refine ⟨⟨(μ : Measure X).prod (ν : Measure X), inferInstance⟩, ?_⟩
    change ((μ : Measure X).prod (ν : Measure X)).map Prod.fst = (μ : Measure X) ∧
      ((μ : Measure X).prod (ν : Measure X)).map Prod.snd = (ν : Measure X)
    simp
  obtain ⟨γ,hγ,hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne
    (couplings_compact μ ν) ((transportCost_lsc p hp).lowerSemicontinuousOn S)
  refine ⟨γ,hγ,le_trans ?_ hC⟩
  apply le_iInf
  intro κ
  apply le_iInf
  intro hκ
  haveI : IsProbabilityMeasure (κ.map Prod.fst) := hκ.1.symm ▸ μ.property
  haveI : IsProbabilityMeasure κ := Measure.isProbabilityMeasure_of_map Prod.fst
  exact (isMinOn_iff.mp hmin) ⟨κ,inferInstance⟩ hκ

lemma ball_representation [ProperSpace X] (p r : ℝ) (hp : 0 < p)
    (ν : ProbabilityMeasure X) :
    wassersteinBall p r ν = first ''
      {γ : ProbabilityMeasure (X × X) | second γ = ν ∧
        transportCost p γ ≤ (ENNReal.ofReal r) ^ p} := by
  ext μ
  constructor
  · intro hμ
    have hi : (⨅ κ ∈ couplings (μ : Measure X) (ν : Measure X),
      ∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ p) ∂κ) ≤ (ENNReal.ofReal r) ^ p := by
      apply (ENNReal.rpow_inv_le_iff hp).mp
      simpa only [wassersteinBall, wassersteinDist, mem_setOf_eq, one_div] using hμ
    obtain ⟨γ,hγ,hcost⟩ := exists_coupling_cost_le p hp.le μ ν _ hi
    have hc := (coupling_iff γ μ ν).mp hγ
    exact ⟨γ,⟨hc.2,hcost⟩,hc.1⟩
  · rintro ⟨γ,⟨hsecond,hcost⟩,rfl⟩
    have hc := (coupling_iff γ (first γ) ν).mpr ⟨rfl,hsecond⟩
    change (⨅ κ ∈ couplings ((first γ : ProbabilityMeasure X) : Measure X)
      (ν : Measure X), ∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ p) ∂κ) ^ (1 / p)
      ≤ ENNReal.ofReal r
    rw [one_div]
    apply (ENNReal.rpow_inv_le_iff hp).mpr
    exact (iInf_le_of_le (γ : Measure (X × X)) (iInf_le_of_le hc le_rfl)).trans hcost

end CouplingResearch

#print axioms CouplingResearch.ball_representation

/-- Weak compactness of a positive-radius Wasserstein ball on a proper metric
space, for a center with finite p-th moment and p ≥ 1. -/
theorem solution {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] (p r : ℝ) (hp : 1 ≤ p) (hr : 0 < r)
    (ν : ProbabilityMeasure X) (hν : HasFinitePthMoment p (ν : Measure X)) :
    IsCompact (wassersteinBall p r ν) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let S : Set (ProbabilityMeasure (X × X)) :=
    {γ | CouplingResearch.second γ = ν ∧
      CouplingResearch.transportCost p γ ≤ (ENNReal.ofReal r) ^ p}
  have hrep : wassersteinBall p r ν = CouplingResearch.first '' S :=
    CouplingResearch.ball_representation p r hp0 ν
  have hs : IsClosed S :=
    (isClosed_eq CouplingResearch.second_continuous continuous_const).inter
      ((lowerSemicontinuous_iff_isClosed_preimage.mp
        (CouplingResearch.transportCost_lsc p hp0.le)) _)
  have htBall := (ReusedTightness.solution p r hp hr ν hν).1
  have ht : IsTightMeasureSet ((fun γ : ProbabilityMeasure (X × X) =>
      (γ : Measure (X × X))) '' S) := by
    apply CouplingResearch.joint_tight
    · apply htBall.subset
      rintro m ⟨γ,hγ,rfl⟩
      refine ⟨CouplingResearch.first γ, ?_, rfl⟩
      rw [hrep]
      exact ⟨γ,hγ,rfl⟩
    · apply (isTightMeasureSet_singleton (μ := (ν : Measure X))).subset
      rintro m ⟨γ,hγ,rfl⟩
      simp only [mem_singleton_iff]
      exact congrArg (fun μ : ProbabilityMeasure X => (μ : Measure X)) hγ.1
  have hc : IsCompact S := by
    simpa only [hs.closure_eq] using isCompact_closure_of_isTightMeasureSet ht
  rw [hrep]
  exact hc.image CouplingResearch.first_continuous

#print axioms solution

end AcceptedCompactness

namespace AttainmentAssembly
open WassersteinLinOpt.Ball

theorem center_mem {X : Type*} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (p r : ℝ) (hp : 0 < p) (hr : 0 ≤ r) (ν : ProbabilityMeasure X) :
    ν ∈ wassersteinBall p r ν := by
  let γ : Measure (X × X) := (ν : Measure X).map (fun x => (x,x))
  have hd : Measurable (fun x : X => (x,x)) := measurable_id.prodMk measurable_id
  have hγ : γ ∈ couplings (ν : Measure X) (ν : Measure X) := by
    constructor
    · rw [Measure.map_map measurable_fst hd]
      simp [Function.comp_def]
    · rw [Measure.map_map measurable_snd hd]
      simp [Function.comp_def]
  have hm : Measurable (fun z : X × X => ENNReal.ofReal (dist z.1 z.2 ^ p)) := by
    fun_prop
  have hc : (∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ p) ∂γ) = 0 := by
    rw [lintegral_map hm hd]
    simp [Real.zero_rpow (ne_of_gt hp)]
  have hi : (⨅ η ∈ couplings (ν : Measure X) (ν : Measure X),
      ∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ p) ∂η) = 0 := by
    apply le_antisymm _ bot_le
    exact iInf_le_of_le γ (iInf_le_of_le hγ hc.le)
  simp [wassersteinBall,wassersteinDist,hi,ENNReal.zero_rpow_of_pos (inv_pos.mpr hp)]

end AttainmentAssembly

open WassersteinLinOpt.Ball

theorem solution {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] (p r : ℝ) (hp : 1 ≤ p) (hr : 0 < r)
    (ν : ProbabilityMeasure X) (hν : HasFinitePthMoment p (ν : Measure X))
    (f : X → ℝ) (hf : UpperSemicontinuous f)
    (hquasi : ∀ μ ∈ wassersteinBall p r ν,
      ∫⁻ x, ENNReal.ofReal (f x) ∂(μ : Measure X) < ⊤ ∨
        ∫⁻ x, ENNReal.ofReal (-f x) ∂(μ : Measure X) < ⊤)
    (x₀ : X) (c q : ℝ) (hc : 0 < c) (hq : 0 < q) (hqp : q < p)
    (hgrowth : ∀ x : X, f x ≤ c * (1 + dist x x₀ ^ q)) :
    ∃ μ ∈ wassersteinBall p r ν,
      quasiIntegral f (μ : Measure X) = optimalValue p r ν f := by
  let S := wassersteinBall p r ν
  have hcompact : IsCompact S := AcceptedCompactness.solution p r hp hr ν hν
  have hνS : ν ∈ S := AttainmentAssembly.center_mem p r (lt_of_lt_of_le zero_lt_one hp) hr.le ν
  letI : Nonempty S := ⟨⟨ν,hνS⟩⟩
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hcompact
  obtain ⟨M,hM,hbound⟩ := AcceptedCompactness.ReusedTightness.ReusedUniformMoment.solution p r hp hr ν hν x₀
  let F : S → EReal := fun μ => quasiIntegral f (μ.val : Measure X)
  have hF : UpperSemicontinuous F := by
    apply upperSemicontinuous_iff_isClosed_preimage.mpr
    intro a
    apply IsSeqClosed.isClosed
    intro μs μ hms hlim
    have hlim' : Tendsto (fun k => (μs k).val) atTop (nhds μ.val) :=
      continuous_subtype_val.continuousAt.tendsto.comp hlim
    have hu := MomentPortmanteau.subpower_limsup hlim' f hf x₀ c p q M hc hq hqp hM
      (hbound μ.val μ.property) (fun k => hbound (μs k).val (μs k).property) hgrowth
    have hl : a ≤ limsup (fun k => F (μs k)) atTop := by
      have hmle : ∀ n, a ≤ F (μs n) := fun n => hms n
      have hh : limsup (fun _ : ℕ => a) atTop ≤ limsup (fun k => F (μs k)) atTop :=
        limsup_le_limsup (Eventually.of_forall hmle)
      simpa only [limsup_const] using hh
    exact hl.trans hu
  obtain ⟨μ,_,hmax⟩ := (hF.upperSemicontinuousOn Set.univ).exists_isMaxOn Set.univ_nonempty isCompact_univ
  refine ⟨μ.val,μ.property,le_antisymm ?_ ?_⟩
  · exact le_iSup_of_le μ.val (le_iSup_of_le μ.property le_rfl)
  · apply iSup_le
    intro η
    apply iSup_le
    intro hη
    exact hmax (Set.mem_univ (⟨η,hη⟩ : S))

#print axioms solution

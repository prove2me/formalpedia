-- Prove2me | solution 1 for TeschlQM.SturmLiouville.variation_of_constants
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-04T18:41:46.826986+00:00
-- url     : https://prove2.me/submissions/f9a809eb-b066-4def-9d35-8070c633135e

import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_SolvesTau
import Definitions.Def_TeschlQM_SturmLiouville_wronskian

open MeasureTheory Set

namespace VoCAux

theorem prod_rule_real (a a' c c' : ℝ → ℝ) (x y : ℝ)
    (ha' : IntervalIntegrable a' volume x y) (hc' : IntervalIntegrable c' volume x y)
    (ha : ∀ t ∈ uIcc x y, a t = a x + ∫ s in x..t, a' s)
    (hc : ∀ t ∈ uIcc x y, c t = c x + ∫ s in x..t, c' s) :
    ∫ t in x..y, (a' t * c t + a t * c' t) = a y * c y - a x * c x := by
  set A : ℝ → ℝ := fun t => a x + ∫ s in x..t, a' s with hAdef
  set C : ℝ → ℝ := fun t => c x + ∫ s in x..t, c' s with hCdef
  have hxm : x ∈ uIcc x y := left_mem_uIcc
  have hym : y ∈ uIcc x y := right_mem_uIcc
  have hA : AbsolutelyContinuousOnInterval A x y := by
    have h1 := ha'.absolutelyContinuousOnInterval_intervalIntegral hxm
    have h2 : AbsolutelyContinuousOnInterval (fun _ : ℝ => a x) x y :=
      (LipschitzWith.const (a x)).lipschitzOnWith.absolutelyContinuousOnInterval
    exact h2.add h1
  have hC : AbsolutelyContinuousOnInterval C x y := by
    have h1 := hc'.absolutelyContinuousOnInterval_intervalIntegral hxm
    have h2 : AbsolutelyContinuousOnInterval (fun _ : ℝ => c x) x y :=
      (LipschitzWith.const (c x)).lipschitzOnWith.absolutelyContinuousOnInterval
    exact h2.add h1
  have key := hA.integral_deriv_mul_eq_sub hC
  have hAy : A y = a y := (ha y hym).symm
  have hAx : A x = a x := by simp [hAdef]
  have hCy : C y = c y := (hc y hym).symm
  have hCx : C x = c x := by simp [hCdef]
  rw [hAy, hAx, hCy, hCx] at key
  rw [← key]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ha'.ae_hasDerivAt_integral, hc'.ae_hasDerivAt_integral] with t h1 h2 ht
  have htI : t ∈ uIcc x y := uIoc_subset_uIcc ht
  have dA : deriv A t = a' t := by
    have := (h1 htI x hxm).const_add (a x)
    exact this.deriv
  have dC : deriv C t = c' t := by
    have := (h2 htI x hxm).const_add (c x)
    exact this.deriv
  rw [dA, dC]
  have e1 : A t = a t := (ha t htI).symm
  have e2 : C t = c t := (hc t htI).symm
  rw [e1, e2]

theorem continuousOn_of_primitive {F F' : ℝ → ℂ} {x y : ℝ}
    (hF' : IntervalIntegrable F' volume x y)
    (hF : ∀ t ∈ uIcc x y, F t = F x + ∫ s in x..t, F' s) : ContinuousOn F (uIcc x y) := by
  have h1 : ContinuousOn (fun t => F x + ∫ s in x..t, F' s) (uIcc x y) :=
    continuousOn_const.add (intervalIntegral.continuousOn_primitive_interval' hF' left_mem_uIcc)
  exact h1.congr hF

theorem re_intervalIntegral {f : ℝ → ℂ} {x t : ℝ} (h : IntervalIntegrable f volume x t) :
    (∫ s in x..t, f s).re = ∫ s in x..t, (f s).re := by
  have := Complex.reCLM.intervalIntegral_comp_comm h
  simpa using this.symm

theorem im_intervalIntegral {f : ℝ → ℂ} {x t : ℝ} (h : IntervalIntegrable f volume x t) :
    (∫ s in x..t, f s).im = ∫ s in x..t, (f s).im := by
  have := Complex.imCLM.intervalIntegral_comp_comm h
  simpa using this.symm

theorem iiRe {f : ℝ → ℂ} {x y : ℝ} (h : IntervalIntegrable f volume x y) :
    IntervalIntegrable (fun s => (f s).re) volume x y := by
  rw [intervalIntegrable_iff] at h ⊢
  exact h.re

theorem iiIm {f : ℝ → ℂ} {x y : ℝ} (h : IntervalIntegrable f volume x y) :
    IntervalIntegrable (fun s => (f s).im) volume x y := by
  rw [intervalIntegrable_iff] at h ⊢
  exact h.im

theorem re_primitive {F F' : ℝ → ℂ} {x y : ℝ}
    (hF' : IntervalIntegrable F' volume x y)
    (hF : ∀ t ∈ uIcc x y, F t = F x + ∫ s in x..t, F' s) :
    ∀ t ∈ uIcc x y, (F t).re = (F x).re + ∫ s in x..t, (F' s).re := by
  intro t ht
  have hi : IntervalIntegrable F' volume x t :=
    hF'.mono_set (uIcc_subset_uIcc left_mem_uIcc ht)
  rw [hF t ht, Complex.add_re, re_intervalIntegral hi]

theorem im_primitive {F F' : ℝ → ℂ} {x y : ℝ}
    (hF' : IntervalIntegrable F' volume x y)
    (hF : ∀ t ∈ uIcc x y, F t = F x + ∫ s in x..t, F' s) :
    ∀ t ∈ uIcc x y, (F t).im = (F x).im + ∫ s in x..t, (F' s).im := by
  intro t ht
  have hi : IntervalIntegrable F' volume x t :=
    hF'.mono_set (uIcc_subset_uIcc left_mem_uIcc ht)
  rw [hF t ht, Complex.add_im, im_intervalIntegral hi]

/-- Product rule (integration by parts) for complex-valued functions given as primitives of
interval integrable functions. -/
theorem prod_rule_complex (F F' G G' : ℝ → ℂ) (x y : ℝ)
    (hF' : IntervalIntegrable F' volume x y) (hG' : IntervalIntegrable G' volume x y)
    (hF : ∀ t ∈ uIcc x y, F t = F x + ∫ s in x..t, F' s)
    (hG : ∀ t ∈ uIcc x y, G t = G x + ∫ s in x..t, G' s) :
    ∫ t in x..y, (F' t * G t + F t * G' t) = F y * G y - F x * G x := by
  have cF := continuousOn_of_primitive hF' hF
  have cG := continuousOn_of_primitive hG' hG
  have cFr : ContinuousOn (fun t => (F t).re) (uIcc x y) := Complex.continuous_re.comp_continuousOn cF
  have cFi : ContinuousOn (fun t => (F t).im) (uIcc x y) := Complex.continuous_im.comp_continuousOn cF
  have cGr : ContinuousOn (fun t => (G t).re) (uIcc x y) := Complex.continuous_re.comp_continuousOn cG
  have cGi : ContinuousOn (fun t => (G t).im) (uIcc x y) := Complex.continuous_im.comp_continuousOn cG
  have iH : IntervalIntegrable (fun t => F' t * G t + F t * G' t) volume x y :=
    (hF'.mul_continuousOn cG).add (hG'.continuousOn_mul cF)
  have rr := prod_rule_real (fun t => (F t).re) (fun t => (F' t).re) (fun t => (G t).re)
    (fun t => (G' t).re) x y (iiRe hF') (iiRe hG') (re_primitive hF' hF) (re_primitive hG' hG)
  have ii := prod_rule_real (fun t => (F t).im) (fun t => (F' t).im) (fun t => (G t).im)
    (fun t => (G' t).im) x y (iiIm hF') (iiIm hG') (im_primitive hF' hF) (im_primitive hG' hG)
  have ri := prod_rule_real (fun t => (F t).re) (fun t => (F' t).re) (fun t => (G t).im)
    (fun t => (G' t).im) x y (iiRe hF') (iiIm hG') (re_primitive hF' hF) (im_primitive hG' hG)
  have ir := prod_rule_real (fun t => (F t).im) (fun t => (F' t).im) (fun t => (G t).re)
    (fun t => (G' t).re) x y (iiIm hF') (iiRe hG') (im_primitive hF' hF) (re_primitive hG' hG)
  have irr : IntervalIntegrable (fun t => (F' t).re * (G t).re + (F t).re * (G' t).re) volume x y :=
    ((iiRe hF').mul_continuousOn cGr).add ((iiRe hG').continuousOn_mul cFr)
  have iii : IntervalIntegrable (fun t => (F' t).im * (G t).im + (F t).im * (G' t).im) volume x y :=
    ((iiIm hF').mul_continuousOn cGi).add ((iiIm hG').continuousOn_mul cFi)
  have iri : IntervalIntegrable (fun t => (F' t).re * (G t).im + (F t).re * (G' t).im) volume x y :=
    ((iiRe hF').mul_continuousOn cGi).add ((iiIm hG').continuousOn_mul cFr)
  have iir : IntervalIntegrable (fun t => (F' t).im * (G t).re + (F t).im * (G' t).re) volume x y :=
    ((iiIm hF').mul_continuousOn cGr).add ((iiRe hG').continuousOn_mul cFi)
  apply Complex.ext
  · rw [re_intervalIntegral iH]
    have : (fun t => (F' t * G t + F t * G' t).re) = fun t =>
        ((F' t).re * (G t).re + (F t).re * (G' t).re) -
          ((F' t).im * (G t).im + (F t).im * (G' t).im) := by
      funext t; simp only [Complex.add_re, Complex.mul_re]; ring
    rw [this, intervalIntegral.integral_sub irr iii]
    try simp only at rr ii
    rw [rr, ii]
    simp only [Complex.sub_re, Complex.mul_re]; ring
  · rw [im_intervalIntegral iH]
    have : (fun t => (F' t * G t + F t * G' t).im) = fun t =>
        ((F' t).re * (G t).im + (F t).re * (G' t).im) +
          ((F' t).im * (G t).re + (F t).im * (G' t).re) := by
      funext t; simp only [Complex.add_im, Complex.mul_im]; ring
    rw [this, intervalIntegral.integral_add iri iir]
    try simp only at ri ir
    rw [ri, ir]
    simp only [Complex.sub_im, Complex.mul_im]; ring


theorem prod_integrand_ii (F F' G G' : ℝ → ℂ) (x y : ℝ)
    (hF' : IntervalIntegrable F' volume x y) (hG' : IntervalIntegrable G' volume x y)
    (hF : ∀ t ∈ uIcc x y, F t = F x + ∫ s in x..t, F' s)
    (hG : ∀ t ∈ uIcc x y, G t = G x + ∫ s in x..t, G' s) :
    IntervalIntegrable (fun t => F' t * G t + F t * G' t) volume x y :=
  (hF'.mul_continuousOn (continuousOn_of_primitive hG' hG)).add
    (hG'.continuousOn_mul (continuousOn_of_primitive hF' hF))

open TeschlQM.SturmLiouville

theorem uIcc_subset_I (L : SLData) {x y : ℝ} (hx : x ∈ L.I) (hy : y ∈ L.I) :
    uIcc x y ⊆ L.I := by
  intro t ht
  rcases ht with ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · rcases le_total x y with h | h
    · rw [min_eq_left h] at h1
      exact lt_of_lt_of_le hx.1 (EReal.coe_le_coe_iff.mpr h1)
    · rw [min_eq_right h] at h1
      exact lt_of_lt_of_le hy.1 (EReal.coe_le_coe_iff.mpr h1)
  · rcases le_total x y with h | h
    · rw [max_eq_right h] at h2
      exact lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr h2) hy.2
    · rw [max_eq_left h] at h2
      exact lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr h2) hx.2

theorem ii_of_loc (L : SLData) {h : ℝ → ℂ} (hh : LocallyIntegrableOn h L.I) {x y : ℝ}
    (hx : x ∈ L.I) (hy : y ∈ L.I) : IntervalIntegrable h volume x y := by
  rw [intervalIntegrable_iff]
  exact (hh.integrableOn_compact_subset (uIcc_subset_I L hx hy) isCompact_uIcc).mono_set
    uIoc_subset_uIcc

theorem primitive_of (L : SLData) {F F' : ℝ → ℂ} {c x : ℝ} (hc : c ∈ L.I) (hx : x ∈ L.I)
    (hF : ∀ s ∈ L.I, ∀ t ∈ L.I, F t - F s = ∫ r in s..t, F' r) :
    ∀ t ∈ uIcc c x, F t = F c + ∫ s in c..t, F' s := by
  intro t ht
  have := hF c hc t (uIcc_subset_I L hc hx ht)
  rw [← this]; ring

/-- Derivative of the Wronskian: if `(τ − z) f = g` and `(τ − z) u = 0`, then
`W_x(f, u) − W_c(f, u) = ∫_c^x u g r`. -/
theorem wronskian_sub (L : SLData) (z : ℂ) (g f u : ℝ → ℂ)
    (hf : IsSolution L z g f) (hu : IsSolution L z 0 u) {c x : ℝ} (hc : c ∈ L.I)
    (hx : x ∈ L.I) :
    wronskian L x f u - wronskian L c f u = ∫ y in c..x, u y * g y * (L.r y : ℂ) := by
  obtain ⟨⟨-, hfl1, hfp1⟩, hfl2, hfp2⟩ := hf
  obtain ⟨⟨-, hul1, hup1⟩, hul2, hup2⟩ := hu
  have i1 := ii_of_loc L hfl1 hc hx
  have i2 := ii_of_loc L hfl2 hc hx
  have j1 := ii_of_loc L hul1 hc hx
  have j2 := ii_of_loc L hul2 hc hx
  have pf1 := primitive_of L hc hx hfp1
  have pf2 := primitive_of L hc hx hfp2
  have pu1 := primitive_of L hc hx hup1
  have pu2 := primitive_of L hc hx hup2
  have e1 := prod_rule_complex _ _ _ _ c x i1 j2 pf1 pu2
  have e2 := prod_rule_complex _ _ _ _ c x i2 j1 pf2 pu1
  have k1 := prod_integrand_ii _ _ _ _ c x i1 j2 pf1 pu2
  have k2 := prod_integrand_ii _ _ _ _ c x i2 j1 pf2 pu1
  have hW : wronskian L x f u - wronskian L c f u =
      (f x * quasiDeriv L u x - f c * quasiDeriv L u c) -
        (quasiDeriv L f x * u x - quasiDeriv L f c * u c) := by
    unfold wronskian; ring
  rw [hW, ← e1, ← e2, ← intervalIntegral.integral_sub k1 k2]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [Pi.zero_apply, add_zero]
  ring

end VoCAux

open TeschlQM.SturmLiouville MeasureTheory

theorem solution (L : SLData) (z : ℂ) (g : ℝ → ℂ)
    (hg : LocallyIntegrableOn (fun x => (L.r x : ℂ) * g x) L.I)
    (u₁ u₂ : ℝ → ℂ) (h₁ : IsSolution L z 0 u₁) (h₂ : IsSolution L z 0 u₂)
    (hW : ∀ x ∈ L.I, wronskian L x u₁ u₂ = 1)
    (c : ℝ) (hc : c ∈ L.I) (f : ℝ → ℂ) (hf : IsSolution L z g f) :
    ∃ α β : ℂ, ∀ x ∈ L.I,
      f x = u₁ x * (α + ∫ y in c..x, u₂ y * g y * (L.r y : ℂ)) +
        u₂ x * (β - ∫ y in c..x, u₁ y * g y * (L.r y : ℂ)) ∧
      quasiDeriv L f x = quasiDeriv L u₁ x * (α + ∫ y in c..x, u₂ y * g y * (L.r y : ℂ)) +
        quasiDeriv L u₂ x * (β - ∫ y in c..x, u₁ y * g y * (L.r y : ℂ)) := by
  refine ⟨wronskian L c f u₂, -wronskian L c f u₁, fun x hx => ?_⟩
  have hA := VoCAux.wronskian_sub L z g f u₂ hf h₂ hc hx
  have hB := VoCAux.wronskian_sub L z g f u₁ hf h₁ hc hx
  have hA' : wronskian L c f u₂ + ∫ y in c..x, u₂ y * g y * (L.r y : ℂ) =
      wronskian L x f u₂ := by rw [← hA]; ring
  have hB' : -wronskian L c f u₁ - ∫ y in c..x, u₁ y * g y * (L.r y : ℂ) =
      -wronskian L x f u₁ := by rw [← hB]; ring
  have h1 := hW x hx
  rw [hA', hB']
  unfold wronskian at h1 ⊢
  constructor
  · linear_combination (-(f x)) * h1
  · linear_combination (-(quasiDeriv L f x)) * h1

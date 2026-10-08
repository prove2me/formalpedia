-- Prove2me | solution 1 for TeschlQM.SturmLiouville.lagrange_identity
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-04T19:01:36.569002+00:00
-- url     : https://prove2.me/submissions/66e70558-c905-44ed-b804-48e4fa620fdb

import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_maxDomain
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

open MeasureTheory Set Filter Topology

namespace LagAux

open TeschlQM.SturmLiouville VoCAux

theorem I_isOpen (L : SLData) : IsOpen L.I := by
  have h1 : IsOpen {x : ℝ | L.a < (x : EReal)} :=
    isOpen_lt continuous_const continuous_coe_real_ereal
  have h2 : IsOpen {x : ℝ | (x : EReal) < L.b} :=
    isOpen_lt continuous_coe_real_ereal continuous_const
  exact h1.inter h2

theorem ae_zero_local_real {k : ℝ → ℝ} {s t : ℝ} (hk : IntervalIntegrable k volume s t)
    (h0 : ∀ x ∈ Icc s t, ∫ u in s..x, k u = 0) :
    ∀ᵐ u ∂(volume.restrict (Ioo s t)), k u = 0 := by
  have hd := hk.ae_hasDerivAt_integral
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hd] with u hu hdu
  have hst : s ≤ t := (hu.1.trans hu.2).le
  have huI : u ∈ uIcc s t := by rw [uIcc_of_le hst]; exact Ioo_subset_Icc_self hu
  have hsI : s ∈ uIcc s t := left_mem_uIcc
  have h1 := hdu huI s hsI
  have hev : (fun x => ∫ v in s..x, k v) =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with x hx
    exact h0 x (Ioo_subset_Icc_self hx)
  have h2 : HasDerivAt (fun x => ∫ v in s..x, k v) 0 u :=
    (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq hev
  exact h1.unique h2

theorem ae_zero_local {h : ℝ → ℂ} {s t : ℝ} (hh : IntervalIntegrable h volume s t)
    (h0 : ∀ x ∈ Icc s t, ∫ u in s..x, h u = 0) :
    ∀ᵐ u ∂(volume.restrict (Ioo s t)), h u = 0 := by
  have hre := ae_zero_local_real (iiRe hh) (fun x hx => by
    have hx' : IntervalIntegrable h volume s x := hh.mono_set (by
      rw [uIcc_of_le hx.1, uIcc_of_le (hx.1.trans hx.2)]
      exact Icc_subset_Icc le_rfl hx.2)
    rw [← re_intervalIntegral hx', h0 x hx, Complex.zero_re])
  have him := ae_zero_local_real (iiIm hh) (fun x hx => by
    have hx' : IntervalIntegrable h volume s x := hh.mono_set (by
      rw [uIcc_of_le hx.1, uIcc_of_le (hx.1.trans hx.2)]
      exact Icc_subset_Icc le_rfl hx.2)
    rw [← im_intervalIntegral hx', h0 x hx, Complex.zero_im])
  filter_upwards [hre, him] with u h1 h2
  exact Complex.ext h1 h2

theorem exists_Icc_subset_I (L : SLData) {x : ℝ} (hx : x ∈ L.I) :
    ∃ s t, s < x ∧ x < t ∧ s ∈ L.I ∧ t ∈ L.I := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (I_isOpen L) x hx
  refine ⟨x - ε / 2, x + ε / 2, by linarith, by linarith, hball ?_, hball ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
  · rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith

theorem continuousOn_of_ACloc (L : SLData) {f1 : ℝ → ℂ} (hf : IsACloc L.I f1) {s t : ℝ}
    (hs : s ∈ L.I) (ht : t ∈ L.I) : ContinuousOn f1 (uIcc s t) := by
  obtain ⟨h, hloc, hprim⟩ := hf
  exact continuousOn_of_primitive (ii_of_loc L hloc hs ht) (primitive_of L hs ht hprim)

/-- Uniqueness of the quasi-derivative on `I`. -/
theorem qd_unique (L : SLData) {f f1 f2 : ℝ → ℂ} (h1 : IsQuasiDerivative L f f1)
    (h2 : IsQuasiDerivative L f f2) : ∀ x ∈ L.I, f1 x = f2 x := by
  intro x hx
  obtain ⟨s, t, hsx, hxt, hs, ht⟩ := exists_Icc_subset_I L hx
  obtain ⟨ac1, l1, p1⟩ := h1
  obtain ⟨ac2, l2, p2⟩ := h2
  have hst : s ≤ t := (hsx.trans hxt).le
  have hsub : Icc s t ⊆ L.I := by
    rw [← uIcc_of_le hst]; exact uIcc_subset_I L hs ht
  have hii := (ii_of_loc L l1 hs ht).sub (ii_of_loc L l2 hs ht)
  have h0 : ∀ y ∈ Icc s t,
      ∫ u in s..y, (f1 u / (L.p u : ℂ) - f2 u / (L.p u : ℂ)) = 0 := by
    intro y hy
    have hyI := hsub hy
    rw [intervalIntegral.integral_sub (ii_of_loc L l1 hs hyI) (ii_of_loc L l2 hs hyI),
      ← p1 s hs y hyI, ← p2 s hs y hyI, sub_self]
  have hae := ae_zero_local hii h0
  have hae2 : f1 =ᵐ[volume.restrict (Ioo s t)] f2 := by
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with u hu hmem
    have huI : u ∈ L.I := hsub (Ioo_subset_Icc_self hmem)
    have hp : (L.p u : ℂ) ≠ 0 := by
      exact_mod_cast (L.p_pos u huI.1 huI.2).ne'
    rw [← sub_div, div_eq_zero_iff] at hu
    rcases hu with hu | hu
    · exact sub_eq_zero.mp hu
    · exact absurd hu hp
  have c1 := (continuousOn_of_ACloc L ac1 hs ht).mono
    (show Ioo s t ⊆ uIcc s t by rw [uIcc_of_le hst]; exact Ioo_subset_Icc_self)
  have c2 := (continuousOn_of_ACloc L ac2 hs ht).mono
    (show Ioo s t ⊆ uIcc s t by rw [uIcc_of_le hst]; exact Ioo_subset_Icc_self)
  exact Measure.eqOn_open_of_ae_eq hae2 isOpen_Ioo c1 c2 ⟨hsx, hxt⟩

theorem locInt_conj {h : ℝ → ℂ} {S : Set ℝ} (hh : LocallyIntegrableOn h S) :
    LocallyIntegrableOn (fun x => starRingEnd ℂ (h x)) S :=
  (Complex.conjCLE.toContinuousLinearMap).locallyIntegrableOn_comp hh

theorem intervalIntegral_conj' (h : ℝ → ℂ) (x y : ℝ) :
    ∫ t in x..y, starRingEnd ℂ (h t) = starRingEnd ℂ (∫ t in x..y, h t) :=
  intervalIntegral.intervalIntegral_conj

theorem isQD_conj (L : SLData) {f f1 : ℝ → ℂ} (hf : IsQuasiDerivative L f f1) :
    IsQuasiDerivative L (fun x => starRingEnd ℂ (f x)) (fun x => starRingEnd ℂ (f1 x)) := by
  obtain ⟨⟨h, hl, hp⟩, hl2, hp2⟩ := hf
  refine ⟨⟨fun x => starRingEnd ℂ (h x), locInt_conj hl, fun x hx y hy => ?_⟩, ?_, ?_⟩
  · rw [intervalIntegral_conj', ← hp x hx y hy, map_sub]
  · have e : (fun t => starRingEnd ℂ (f1 t) / (L.p t : ℂ)) =
        fun t => starRingEnd ℂ (f1 t / (L.p t : ℂ)) := by
      funext t; simp [map_div₀, Complex.conj_ofReal]
    rw [e]; exact locInt_conj hl2
  · intro x hx y hy
    have e : (fun t => starRingEnd ℂ (f1 t) / (L.p t : ℂ)) =
        fun t => starRingEnd ℂ (f1 t / (L.p t : ℂ)) := by
      funext t; simp [map_div₀, Complex.conj_ofReal]
    rw [e, intervalIntegral_conj', ← hp2 x hx y hy, map_sub]

theorem isQD_quasiDeriv (L : SLData) {f f1 : ℝ → ℂ} (hf : IsQuasiDerivative L f f1) :
    IsQuasiDerivative L f (quasiDeriv L f) := by
  have hex : ∃ f1, IsQuasiDerivative L f f1 := ⟨f1, hf⟩
  unfold quasiDeriv
  rw [dif_pos hex]
  exact hex.choose_spec

theorem quasiDeriv_conj (L : SLData) {f : ℝ → ℂ}
    (hf : IsQuasiDerivative L f (quasiDeriv L f)) :
    ∀ x ∈ L.I, quasiDeriv L (fun y => starRingEnd ℂ (f y)) x =
      starRingEnd ℂ (quasiDeriv L f x) :=
  qd_unique L (isQD_quasiDeriv L (isQD_conj L hf)) (isQD_conj L hf)

theorem solvesTau_conj (L : SLData) {g G : ℝ → ℂ} (hg : SolvesTau L g G) :
    SolvesTau L (fun x => starRingEnd ℂ (g x)) (fun x => starRingEnd ℂ (G x)) := by
  obtain ⟨hq, hl, hp⟩ := hg
  have hc := quasiDeriv_conj L hq
  refine ⟨isQD_quasiDeriv L (isQD_conj L hq), ?_, ?_⟩
  · have e : (fun t => (L.q t : ℂ) * starRingEnd ℂ (g t) - (L.r t : ℂ) * starRingEnd ℂ (G t)) =
        fun t => starRingEnd ℂ ((L.q t : ℂ) * g t - (L.r t : ℂ) * G t) := by
      funext t; simp [Complex.conj_ofReal]
    rw [e]; exact locInt_conj hl
  · intro x hx y hy
    have e : (fun t => (L.q t : ℂ) * starRingEnd ℂ (g t) - (L.r t : ℂ) * starRingEnd ℂ (G t)) =
        fun t => starRingEnd ℂ ((L.q t : ℂ) * g t - (L.r t : ℂ) * G t) := by
      funext t; simp [Complex.conj_ofReal]
    rw [hc y hy, hc x hx, e, intervalIntegral_conj', ← hp x hx y hy, map_sub]

/-- The Lagrange identity on a compact subinterval:
`W_x(g, f) − W_c(g, f) = ∫_c^x r (G f − g F)`. -/
theorem wronskian_diff (L : SLData) {f g F G : ℝ → ℂ} (hf : SolvesTau L f F)
    (hg : SolvesTau L g G) {c x : ℝ} (hc : c ∈ L.I) (hx : x ∈ L.I) :
    wronskian L x g f - wronskian L c g f =
      ∫ t in c..x, (L.r t : ℂ) * (G t * f t - g t * F t) := by
  obtain ⟨⟨-, hfl1, hfp1⟩, hfl2, hfp2⟩ := hf
  obtain ⟨⟨-, hgl1, hgp1⟩, hgl2, hgp2⟩ := hg
  have i1 := ii_of_loc L hfl1 hc hx
  have i2 := ii_of_loc L hfl2 hc hx
  have j1 := ii_of_loc L hgl1 hc hx
  have j2 := ii_of_loc L hgl2 hc hx
  have pf1 := primitive_of L hc hx hfp1
  have pf2 := primitive_of L hc hx hfp2
  have pg1 := primitive_of L hc hx hgp1
  have pg2 := primitive_of L hc hx hgp2
  have e1 := prod_rule_complex _ _ _ _ c x j1 i2 pg1 pf2
  have e2 := prod_rule_complex _ _ _ _ c x j2 i1 pg2 pf1
  have k1 := prod_integrand_ii _ _ _ _ c x j1 i2 pg1 pf2
  have k2 := prod_integrand_ii _ _ _ _ c x j2 i1 pg2 pf1
  have hW : wronskian L x g f - wronskian L c g f =
      (g x * quasiDeriv L f x - g c * quasiDeriv L f c) -
        (quasiDeriv L g x * f x - quasiDeriv L g c * f c) := by
    unfold wronskian; ring
  rw [hW, ← e1, ← e2, ← intervalIntegral.integral_sub k1 k2]
  apply intervalIntegral.integral_congr
  intro t _
  simp only
  ring

theorem eventually_lt_left (L : SLData) {t : ℝ} (ht : L.a < (t : EReal)) :
    ∀ᶠ x in L.atLeft, x < t := by
  have h1 : Iio (t : EReal) ∈ 𝓝[>] L.a := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht)
  have := Filter.preimage_mem_comap (m := fun x : ℝ => (x : EReal)) h1
  filter_upwards [this] with x hx
  exact EReal.coe_lt_coe_iff.mp hx

theorem eventually_gt_right (L : SLData) {t : ℝ} (ht : (t : EReal) < L.b) :
    ∀ᶠ x in L.atRight, t < x := by
  have h1 : Ioi (t : EReal) ∈ 𝓝[<] L.b := mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ht)
  have := Filter.preimage_mem_comap (m := fun x : ℝ => (x : EReal)) h1
  filter_upwards [this] with x hx
  exact EReal.coe_lt_coe_iff.mp hx

theorem eventually_gt_a (L : SLData) : ∀ᶠ x : ℝ in L.atLeft, L.a < (x : EReal) := by
  have h1 : Ioi L.a ∈ 𝓝[>] L.a := self_mem_nhdsWithin
  have := Filter.preimage_mem_comap (m := fun x : ℝ => (x : EReal)) h1
  filter_upwards [this] with x hx
  exact hx

theorem eventually_lt_b (L : SLData) : ∀ᶠ x : ℝ in L.atRight, (x : EReal) < L.b := by
  have h1 : Iio L.b ∈ 𝓝[<] L.b := self_mem_nhdsWithin
  have := Filter.preimage_mem_comap (m := fun x : ℝ => (x : EReal)) h1
  filter_upwards [this] with x hx
  exact hx

theorem exists_mem_I (L : SLData) : ∃ c, c ∈ L.I := by
  obtain ⟨x, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.mp L.hab
  exact ⟨x, h1, h2⟩

theorem eventually_mem_left (L : SLData) : ∀ᶠ x in L.atLeft, x ∈ L.I := by
  obtain ⟨c, hc⟩ := exists_mem_I L
  filter_upwards [eventually_gt_a L, eventually_lt_left L hc.1] with x h1 h2
  exact ⟨h1, lt_trans (EReal.coe_lt_coe_iff.mpr h2) hc.2⟩

theorem eventually_mem_right (L : SLData) : ∀ᶠ x in L.atRight, x ∈ L.I := by
  obtain ⟨c, hc⟩ := exists_mem_I L
  filter_upwards [eventually_lt_b L, eventually_gt_right L hc.2] with x h1 h2
  exact ⟨lt_trans hc.1 (EReal.coe_lt_coe_iff.mpr h2), h1⟩

instance atLeft_neBot (L : SLData) : L.atLeft.NeBot := by
  apply Filter.comap_neBot
  intro t ht
  rcases (nhdsGT_basis_of_exists_gt ⟨L.b, L.hab⟩).mem_iff.mp ht with ⟨u, hu, hut⟩
  obtain ⟨x, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.mp hu
  exact ⟨x, hut ⟨h1, h2⟩⟩

instance atRight_neBot (L : SLData) : L.atRight.NeBot := by
  apply Filter.comap_neBot
  intro t ht
  rcases (nhdsLT_basis_of_exists_lt ⟨L.a, L.hab⟩).mem_iff.mp ht with ⟨u, hu, hut⟩
  obtain ⟨x, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.mp hu
  exact ⟨x, hut ⟨h1, h2⟩⟩

instance atLeft_cg (L : SLData) : L.atLeft.IsCountablyGenerated := by
  unfold SLData.atLeft; infer_instance

instance atRight_cg (L : SLData) : L.atRight.IsCountablyGenerated := by
  unfold SLData.atRight; infer_instance

theorem integrable_conj_mul (L : SLData) {g F : ℝ → ℂ} (hg : MemLp g 2 L.measure)
    (hF : MemLp F 2 L.measure) :
    Integrable (fun x => starRingEnd ℂ (g x) * F x) L.measure := by
  have h1 : MemLp (star g) 2 L.measure := hg.star
  have := h1.integrable_mul hF
  exact this

theorem r_aemeas (L : SLData) :
    AEMeasurable (fun x => ENNReal.ofReal (L.r x)) (volume.restrict L.I) :=
  L.r_loc.aestronglyMeasurable.aemeasurable.ennreal_ofReal

theorem r_toReal_ae (L : SLData) :
    ∀ᵐ x ∂(volume.restrict L.I), (ENNReal.ofReal (L.r x)).toReal = L.r x := by
  filter_upwards [ae_restrict_mem (I_isOpen L).measurableSet] with x hx
  exact ENNReal.toReal_ofReal (L.r_pos x hx.1 hx.2).le

theorem integrableOn_of_integrable_measure (L : SLData) {h : ℝ → ℂ}
    (hh : Integrable h L.measure) :
    IntegrableOn (fun x => (L.r x : ℂ) * h x) L.I := by
  unfold SLData.measure at hh
  rw [integrable_withDensity_iff_integrable_smul₀' (r_aemeas L)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))] at hh
  refine hh.congr ?_
  filter_upwards [r_toReal_ae L] with x hx
  rw [hx, Complex.real_smul]

theorem integral_measure_eq (L : SLData) (h : ℝ → ℂ) :
    ∫ x, h x ∂L.measure = ∫ x in L.I, (L.r x : ℂ) * h x := by
  unfold SLData.measure
  rw [integral_withDensity_eq_integral_toReal_smul₀ (r_aemeas L)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  refine integral_congr_ae ?_
  filter_upwards [r_toReal_ae L] with x hx
  rw [hx, Complex.real_smul]

theorem tendsto_left (L : SLData) {φ : ℝ → ℂ} (hφ : IntegrableOn φ L.I) {c : ℝ}
    (hc : c ∈ L.I) :
    Tendsto (fun x => ∫ t in x..c, φ t) L.atLeft
      (𝓝 (∫ t in L.I ∩ Iic c, φ t)) := by
  have hmI := (I_isOpen L).measurableSet
  have key : Tendsto (fun x => ∫ t in L.I, (Ioc x c).indicator φ t) L.atLeft
      (𝓝 (∫ t in L.I, (Iic c).indicator φ t)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖φ t‖) ?_ ?_ hφ.norm ?_
    · exact Eventually.of_forall (fun x => hφ.aestronglyMeasurable.indicator measurableSet_Ioc)
    · exact Eventually.of_forall (fun x => Eventually.of_forall
        (fun t => norm_indicator_le_norm_self _ _))
    · filter_upwards [ae_restrict_mem hmI] with t ht
      by_cases htc : t ≤ c
      · have hev := eventually_lt_left L ht.1
        have : (fun x => (Ioc x c).indicator φ t) =ᶠ[L.atLeft] fun _ => (Iic c).indicator φ t := by
          filter_upwards [hev] with x hx
          rw [indicator_of_mem (show t ∈ Ioc x c from ⟨hx, htc⟩),
            indicator_of_mem (show t ∈ Iic c from htc)]
        exact tendsto_const_nhds.congr' this.symm
      · have h1 : ∀ x, (Ioc x c).indicator φ t = 0 := fun x =>
          indicator_of_notMem (fun h => htc h.2) _
        have h2 : (Iic c).indicator φ t = 0 := indicator_of_notMem (show t ∉ Iic c from htc) _
        simp only [h1, h2]
        exact tendsto_const_nhds
  rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    inter_comm] at key
  refine key.congr' ?_
  filter_upwards [eventually_mem_left L, eventually_lt_left L hc.1] with x hx hxc
  rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    intervalIntegral.integral_of_le hxc.le]
  congr 2
  apply inter_eq_left.mpr
  intro t ht
  exact uIcc_subset_I L hx hc (Ioc_subset_Icc_self.trans Icc_subset_uIcc ht)

theorem tendsto_right (L : SLData) {φ : ℝ → ℂ} (hφ : IntegrableOn φ L.I) {c : ℝ}
    (hc : c ∈ L.I) :
    Tendsto (fun x => ∫ t in c..x, φ t) L.atRight
      (𝓝 (∫ t in L.I ∩ Ioi c, φ t)) := by
  have hmI := (I_isOpen L).measurableSet
  have key : Tendsto (fun x => ∫ t in L.I, (Ioc c x).indicator φ t) L.atRight
      (𝓝 (∫ t in L.I, (Ioi c).indicator φ t)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖φ t‖) ?_ ?_ hφ.norm ?_
    · exact Eventually.of_forall (fun x => hφ.aestronglyMeasurable.indicator measurableSet_Ioc)
    · exact Eventually.of_forall (fun x => Eventually.of_forall
        (fun t => norm_indicator_le_norm_self _ _))
    · filter_upwards [ae_restrict_mem hmI] with t ht
      by_cases htc : c < t
      · have hev := eventually_gt_right L ht.2
        have : (fun x => (Ioc c x).indicator φ t) =ᶠ[L.atRight]
            fun _ => (Ioi c).indicator φ t := by
          filter_upwards [hev] with x hx
          rw [indicator_of_mem (show t ∈ Ioc c x from ⟨htc, hx.le⟩),
            indicator_of_mem (show t ∈ Ioi c from htc)]
        exact tendsto_const_nhds.congr' this.symm
      · have h1 : ∀ x, (Ioc c x).indicator φ t = 0 := fun x =>
          indicator_of_notMem (fun h => htc h.1) _
        have h2 : (Ioi c).indicator φ t = 0 := indicator_of_notMem (show t ∉ Ioi c from htc) _
        simp only [h1, h2]
        exact tendsto_const_nhds
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_comm] at key
  refine key.congr' ?_
  filter_upwards [eventually_mem_right L, eventually_gt_right L hc.2] with x hx hxc
  rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    intervalIntegral.integral_of_le hxc.le]
  congr 2
  apply inter_eq_left.mpr
  intro t ht
  exact uIcc_subset_I L hc hx (Ioc_subset_Icc_self.trans Icc_subset_uIcc ht)

end LagAux

open TeschlQM.SturmLiouville MeasureTheory Filter Topology

theorem solution (L : SLData) (f g F G : ℝ → ℂ)
    (hf : MemLp f 2 L.measure) (hg : MemLp g 2 L.measure)
    (hF : SolvesTau L f F) (hG : SolvesTau L g G)
    (hF2 : MemLp F 2 L.measure) (hG2 : MemLp G 2 L.measure) :
    Tendsto (fun x => wronskian L x (fun y => starRingEnd ℂ (g y)) f) L.atLeft
        (𝓝 (wronskianLeft L (fun y => starRingEnd ℂ (g y)) f)) ∧
      Tendsto (fun x => wronskian L x (fun y => starRingEnd ℂ (g y)) f) L.atRight
        (𝓝 (wronskianRight L (fun y => starRingEnd ℂ (g y)) f)) ∧
      Integrable (fun x => starRingEnd ℂ (g x) * F x) L.measure ∧
      Integrable (fun x => starRingEnd ℂ (G x) * f x) L.measure ∧
      ∫ x, starRingEnd ℂ (g x) * F x ∂L.measure =
        wronskianLeft L (fun y => starRingEnd ℂ (g y)) f -
          wronskianRight L (fun y => starRingEnd ℂ (g y)) f +
          ∫ x, starRingEnd ℂ (G x) * f x ∂L.measure := by
  obtain ⟨c, hc⟩ := LagAux.exists_mem_I L
  set gs : ℝ → ℂ := fun y => starRingEnd ℂ (g y) with hgs
  set Gs : ℝ → ℂ := fun y => starRingEnd ℂ (G y) with hGs
  have hGc := LagAux.solvesTau_conj L hG
  have i1 := LagAux.integrable_conj_mul L hg hF2
  have i2 := LagAux.integrable_conj_mul L hG2 hf
  set φ : ℝ → ℂ := fun t => (L.r t : ℂ) * (Gs t * f t - gs t * F t) with hφ
  have hφi : IntegrableOn φ L.I := by
    have := (LagAux.integrableOn_of_integrable_measure L i2).sub
      (LagAux.integrableOn_of_integrable_measure L i1)
    refine this.congr_fun (fun t _ => ?_) (LagAux.I_isOpen L).measurableSet
    simp only [φ, gs, Gs, Pi.sub_apply]; ring
  -- `W_x = W_c - ∫_x^c φ` and `W_x = W_c + ∫_c^x φ`
  have hWl : ∀ x ∈ L.I, wronskian L x gs f = wronskian L c gs f - ∫ t in x..c, φ t := by
    intro x hx
    have := LagAux.wronskian_diff L hF hGc hc hx
    rw [intervalIntegral.integral_symm]
    simp only [φ]
    rw [← this]; ring
  have hWr : ∀ x ∈ L.I, wronskian L x gs f = wronskian L c gs f + ∫ t in c..x, φ t := by
    intro x hx
    have := LagAux.wronskian_diff L hF hGc hc hx
    simp only [φ]
    rw [← this]; ring
  have tl : Tendsto (fun x => wronskian L x gs f) L.atLeft
      (𝓝 (wronskian L c gs f - ∫ t in L.I ∩ Iic c, φ t)) := by
    have := (LagAux.tendsto_left L hφi hc).const_sub (wronskian L c gs f)
    refine this.congr' ?_
    filter_upwards [LagAux.eventually_mem_left L] with x hx
    exact (hWl x hx).symm
  have tr : Tendsto (fun x => wronskian L x gs f) L.atRight
      (𝓝 (wronskian L c gs f + ∫ t in L.I ∩ Ioi c, φ t)) := by
    have := (LagAux.tendsto_right L hφi hc).const_add (wronskian L c gs f)
    refine this.congr' ?_
    filter_upwards [LagAux.eventually_mem_right L] with x hx
    exact (hWr x hx).symm
  have tl' := tendsto_nhds_limUnder ⟨_, tl⟩
  have tr' := tendsto_nhds_limUnder ⟨_, tr⟩
  refine ⟨tl', tr', i1, i2, ?_⟩
  have eL : wronskianLeft L gs f = _ := tendsto_nhds_unique tl' tl
  have eR : wronskianRight L gs f = _ := tendsto_nhds_unique tr' tr
  rw [eL, eR, LagAux.integral_measure_eq, LagAux.integral_measure_eq]
  have hsplit := MeasureTheory.integral_inter_add_diff (s := L.I) (t := Iic c)
    measurableSet_Iic hφi
  have hdiff : L.I \ Iic c = L.I ∩ Ioi c := by
    ext t; simp [not_le]
  rw [hdiff] at hsplit
  have hI : ∫ t in L.I, φ t = (∫ x in L.I, (L.r x : ℂ) * (starRingEnd ℂ (G x) * f x)) -
      ∫ x in L.I, (L.r x : ℂ) * (starRingEnd ℂ (g x) * F x) := by
    rw [← integral_sub (LagAux.integrableOn_of_integrable_measure L i2)
      (LagAux.integrableOn_of_integrable_measure L i1)]
    refine setIntegral_congr_fun (LagAux.I_isOpen L).measurableSet (fun t _ => ?_)
    simp only [φ, gs, Gs]; ring
  linear_combination hsplit + hI

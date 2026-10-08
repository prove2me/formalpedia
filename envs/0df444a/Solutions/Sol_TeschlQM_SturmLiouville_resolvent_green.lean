-- Prove2me | solution 1 for TeschlQM.SturmLiouville.resolvent_green
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-05T18:43:00.505764+00:00
-- url     : https://prove2.me/submissions/c372617f-0ed0-4cf4-a63e-b2e9411d3281

import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_maxDomain
import Definitions.Def_TeschlQM_SturmLiouville_wronskian
import Definitions.Def_TeschlQM_SturmLiouville_SolvesTau
import Definitions.Def_TeschlQM_SturmLiouville_IsSqIntegrableNear
import Definitions.Def_TeschlQM_SturmLiouville_IsLimitCircle
import Definitions.Def_TeschlQM_SturmLiouville_operatorGraph
import Definitions.Def_TeschlQM_SturmLiouville_IsResolventAt

set_option autoImplicit false

section SecBase

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
  fun x hx =>
    (hh x hx).imp fun _ ht => ⟨ht.1, (Complex.conjCLE.toContinuousLinearMap).integrable_comp ht.2⟩

theorem intervalIntegral_conj' (h : ℝ → ℂ) (x y : ℝ) :
    ∫ t in x..y, starRingEnd ℂ (h t) = starRingEnd ℂ (∫ t in x..y, h t) := by
  simp only [intervalIntegral, integral_conj, map_sub]

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


open MeasureTheory Set Filter Topology
open scoped Interval

namespace IvpAux

open VoCAux

theorem J_contOn {a : ℝ → ℝ} {c x : ℝ} (ha : IntervalIntegrable a volume c x) :
    ContinuousOn (fun s => ∫ u in c..s, a u) (uIcc c x) :=
  intervalIntegral.continuousOn_primitive_interval' ha left_mem_uIcc

theorem pow_integral {a : ℝ → ℝ} {c x : ℝ} (ha : IntervalIntegrable a volume c x) (n : ℕ) :
    ∀ t ∈ uIcc c x, (∫ s in c..t, a s) ^ (n + 1) =
      (n + 1) * ∫ s in c..t, a s * (∫ u in c..s, a u) ^ n := by
  induction n with
  | zero => intro t _; simp
  | succ n ih =>
    intro t ht
    have hsub : uIcc c t ⊆ uIcc c x := uIcc_subset_uIcc left_mem_uIcc ht
    have hat : IntervalIntegrable a volume c t := ha.mono_set hsub
    have hJc : ContinuousOn (fun s => ∫ u in c..s, a u) (uIcc c t) := (J_contOn ha).mono hsub
    have i1 : IntervalIntegrable (fun s => ((n : ℝ) + 1) * (a s * (∫ u in c..s, a u) ^ n))
        volume c t :=
      (hat.mul_continuousOn (hJc.pow n)).const_mul _
    have pr := prod_rule_real (fun s => (∫ u in c..s, a u) ^ (n + 1))
      (fun s => ((n : ℝ) + 1) * (a s * (∫ u in c..s, a u) ^ n))
      (fun s => ∫ u in c..s, a u) a c t i1 hat
      (fun s hs => by
        simp only [intervalIntegral.integral_same, zero_pow (Nat.succ_ne_zero n), zero_add]
        rw [intervalIntegral.integral_const_mul]
        exact ih s (hsub hs))
      (fun s _ => by simp)
    simp only [intervalIntegral.integral_same, mul_zero, sub_zero] at pr
    have e : (fun s => ((n : ℝ) + 1) * (a s * (∫ u in c..s, a u) ^ n) * (∫ u in c..s, a u) +
        (∫ u in c..s, a u) ^ (n + 1) * a s) =
        fun s => ((n + 1 : ℕ) + 1 : ℝ) * (a s * (∫ u in c..s, a u) ^ (n + 1)) := by
      funext s; push_cast; ring
    rw [e, intervalIntegral.integral_const_mul] at pr
    rw [pow_succ, ← pr]

theorem K_eq_abs {a : ℝ → ℝ} (ha0 : ∀ t, 0 ≤ a t) (c t : ℝ) :
    ∫ s in Ι c t, a s = |∫ s in c..t, a s| := by
  rw [intervalIntegral.abs_integral_eq_abs_integral_uIoc, abs_of_nonneg]
  exact setIntegral_nonneg measurableSet_uIoc (fun s _ => ha0 s)

theorem K_contOn {a : ℝ → ℝ} (ha0 : ∀ t, 0 ≤ a t) {c x : ℝ}
    (ha : IntervalIntegrable a volume c x) :
    ContinuousOn (fun s => ∫ u in Ι c s, a u) (uIcc c x) := by
  have : (fun s => ∫ u in Ι c s, a u) = fun s => |∫ u in c..s, a u| := by
    funext s; exact K_eq_abs ha0 c s
  rw [this]
  exact (J_contOn ha).abs

theorem K_pow_integral {a : ℝ → ℝ} (ha0 : ∀ t, 0 ≤ a t) {c x : ℝ}
    (ha : IntervalIntegrable a volume c x) (n : ℕ) :
    ∀ t ∈ uIcc c x, ∫ s in Ι c t, a s * (∫ u in Ι c s, a u) ^ n =
      (∫ s in Ι c t, a s) ^ (n + 1) / (n + 1) := by
  intro t ht
  have hP := pow_integral ha n t ht
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  rcases le_total c t with hct | htc
  · have hK : ∫ s in Ι c t, a s = ∫ s in c..t, a s := by
      rw [uIoc_of_le hct, intervalIntegral.integral_of_le hct]
    have hL : ∫ s in Ι c t, a s * (∫ u in Ι c s, a u) ^ n =
        ∫ s in c..t, a s * (∫ u in c..s, a u) ^ n := by
      rw [uIoc_of_le hct, ← intervalIntegral.integral_of_le hct]
      refine intervalIntegral.integral_congr (fun s hs => ?_)
      rw [uIcc_of_le hct] at hs
      show a s * (∫ u in Ι c s, a u) ^ n = a s * (∫ u in c..s, a u) ^ n
      rw [uIoc_of_le hs.1, intervalIntegral.integral_of_le hs.1]
    rw [hL, hK, hP]
    field_simp
  · have hK : ∫ s in Ι c t, a s = -∫ s in c..t, a s := by
      rw [uIoc_of_ge htc, ← intervalIntegral.integral_of_le htc, intervalIntegral.integral_symm]
    have hL : ∫ s in Ι c t, a s * (∫ u in Ι c s, a u) ^ n =
        -((-1) ^ n * ∫ s in c..t, a s * (∫ u in c..s, a u) ^ n) := by
      rw [uIoc_of_ge htc]
      have e : ∫ s in Ioc t c, a s * (∫ u in Ι c s, a u) ^ n =
          ∫ s in Ioc t c, a s * (-(∫ u in c..s, a u)) ^ n := by
        refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
        show a s * (∫ u in Ι c s, a u) ^ n = a s * (-(∫ u in c..s, a u)) ^ n
        rw [uIoc_of_ge hs.2, ← intervalIntegral.integral_of_le hs.2,
          intervalIntegral.integral_symm]
      rw [e, ← intervalIntegral.integral_of_le htc, intervalIntegral.integral_symm,
        ← intervalIntegral.integral_const_mul]
      congr 1
      refine intervalIntegral.integral_congr (fun s _ => ?_)
      show a s * (-(∫ u in c..s, a u)) ^ n = (-1) ^ n * (a s * (∫ u in c..s, a u) ^ n)
      rw [neg_pow]; ring
    rw [hL, hK, neg_pow (∫ s in c..t, a s), hP]
    field_simp
    ring

/-- Gronwall-type iteration bound. -/
theorem iter_bound {a : ℝ → ℝ} (ha0 : ∀ t, 0 ≤ a t) {c x M : ℝ}
    (ha : IntervalIntegrable a volume c x) (φ : ℕ → ℝ → ℝ)
    (hcont : ∀ n, ContinuousOn (φ n) (uIcc c x))
    (h0 : ∀ t ∈ uIcc c x, φ 0 t ≤ M)
    (hstep : ∀ n, ∀ t ∈ uIcc c x, φ (n + 1) t ≤ ∫ s in Ι c t, a s * φ n s) :
    ∀ n, ∀ t ∈ uIcc c x, φ n t ≤ M * (∫ s in Ι c t, a s) ^ n / n.factorial := by
  intro n
  induction n with
  | zero => intro t ht; simpa using h0 t ht
  | succ n ih =>
    intro t ht
    have hsub : uIcc c t ⊆ uIcc c x := uIcc_subset_uIcc left_mem_uIcc ht
    have hIoc : Ι c t ⊆ uIcc c x := uIoc_subset_uIcc.trans hsub
    have haI : IntegrableOn a (Ι c t) := (ha.mono_set hsub).def'
    have hKc := K_contOn ha0 ha
    have i1 : IntegrableOn (fun s => a s * φ n s) (Ι c t) :=
      haI.mul_continuousOn_of_subset (hcont n) measurableSet_uIoc isCompact_uIcc hIoc
    have i2 : IntegrableOn (fun s => a s * (M * (∫ u in Ι c s, a u) ^ n / n.factorial)) (Ι c t) :=
      haI.mul_continuousOn_of_subset (((hKc.pow n).const_smul M).div_const _)
        measurableSet_uIoc isCompact_uIcc hIoc
    calc φ (n + 1) t ≤ ∫ s in Ι c t, a s * φ n s := hstep n t ht
      _ ≤ ∫ s in Ι c t, a s * (M * (∫ u in Ι c s, a u) ^ n / n.factorial) :=
          setIntegral_mono_on i1 i2 measurableSet_uIoc
            (fun s hs => mul_le_mul_of_nonneg_left (ih s (hIoc hs)) (ha0 s))
      _ = M / n.factorial * ∫ s in Ι c t, a s * (∫ u in Ι c s, a u) ^ n := by
          rw [← integral_const_mul]; congr 1; funext s; ring
      _ = M / n.factorial * ((∫ s in Ι c t, a s) ^ (n + 1) / (n + 1)) := by
          rw [K_pow_integral ha0 ha n t ht]
      _ = M * (∫ s in Ι c t, a s) ^ (n + 1) / (n + 1).factorial := by
          rw [Nat.factorial_succ]; push_cast; field_simp

end IvpAux


open MeasureTheory Set Filter Topology
open scoped Interval

namespace IvpAux

open TeschlQM.SturmLiouville VoCAux LagAux

theorem contOn_prim (L : SLData) {h : ℝ → ℂ} (hh : LocallyIntegrableOn h L.I) {c : ℝ}
    (hc : c ∈ L.I) : ContinuousOn (fun x => ∫ t in c..x, h t) L.I := by
  intro x hx
  obtain ⟨s, t, hsx, hxt, hs, ht⟩ := exists_Icc_subset_I L hx
  have h1 : ContinuousOn (fun y => (∫ u in c..s, h u) + ∫ u in s..y, h u) (uIcc s t) :=
    continuousOn_const.add
      (intervalIntegral.continuousOn_primitive_interval' (ii_of_loc L hh hs ht) left_mem_uIcc)
  have h2 : EqOn (fun y => ∫ u in c..y, h u)
      (fun y => (∫ u in c..s, h u) + ∫ u in s..y, h u) (uIcc s t) := by
    intro y hy
    have hyI := uIcc_subset_I L hs ht hy
    exact (intervalIntegral.integral_add_adjacent_intervals (ii_of_loc L hh hc hs)
      (ii_of_loc L hh hs hyI)).symm
  have hnhds : uIcc s t ∈ 𝓝 x := by
    rw [uIcc_of_le (hsx.trans hxt).le]; exact Icc_mem_nhds hsx hxt
  have hxm : x ∈ uIcc s t := mem_of_mem_nhds hnhds
  exact ((h1.congr h2).continuousAt hnhds).continuousWithinAt

theorem locInt_ofReal {f : ℝ → ℝ} {S : Set ℝ} (hf : LocallyIntegrableOn f S) :
    LocallyIntegrableOn (fun x => (f x : ℂ)) S :=
  fun x hx => (hf x hx).imp fun _ ht => ⟨ht.1, Complex.ofRealCLM.integrable_comp ht.2⟩

/-- `1/p` as a complex function. -/
noncomputable def pinv (L : SLData) (t : ℝ) : ℂ := (((L.p t)⁻¹ : ℝ) : ℂ)

theorem pinv_loc (L : SLData) : LocallyIntegrableOn (pinv L) L.I :=
  locInt_ofReal L.p_inv_loc

theorem div_p (L : SLData) (w : ℂ) (t : ℝ) : w / (L.p t : ℂ) = pinv L t * w := by
  unfold pinv; push_cast; ring

theorem q_loc (L : SLData) : LocallyIntegrableOn (fun t => (L.q t : ℂ)) L.I :=
  locInt_ofReal L.q_loc

theorem r_loc' (L : SLData) : LocallyIntegrableOn (fun t => (L.r t : ℂ)) L.I :=
  locInt_ofReal L.r_loc

theorem I_lc (L : SLData) : IsLocallyClosed L.I := (I_isOpen L).isLocallyClosed

/-- The Picard iterates for `(τ - z) f = g`, `f(c) = α`, `(p f')(c) = β`, as pairs `(f, p f')`. -/
noncomputable def pic (L : SLData) (g : ℝ → ℂ) (c : ℝ) (α β : ℂ) : ℕ → ℂ → ℝ → ℂ × ℂ
  | 0 => fun _ _ => (α, β)
  | n + 1 => fun z x =>
    (α + ∫ t in c..x, pinv L t * (pic L g c α β n z t).2,
     β + ∫ t in c..x, (((L.q t : ℂ) - z * (L.r t : ℂ)) * (pic L g c α β n z t).1 -
        (L.r t : ℂ) * g t))

section Picard

variable (L : SLData) (g : ℝ → ℂ) (c : ℝ) (α β : ℂ)

theorem coef_loc (z : ℂ) :
    LocallyIntegrableOn (fun t => (L.q t : ℂ) - z * (L.r t : ℂ)) L.I :=
  (q_loc L).sub ((r_loc' L).continuousOn_mul (continuousOn_const (c := z)) (I_lc L))

theorem pic_contOn (hg : LocallyIntegrableOn (fun x => (L.r x : ℂ) * g x) L.I) (hc : c ∈ L.I) :
    ∀ n z, ContinuousOn (fun x => (pic L g c α β n z x).1) L.I ∧
      ContinuousOn (fun x => (pic L g c α β n z x).2) L.I := by
  intro n
  induction n with
  | zero => intro z; exact ⟨continuousOn_const, continuousOn_const⟩
  | succ n ih =>
    intro z
    obtain ⟨h1, h2⟩ := ih z
    refine ⟨?_, ?_⟩
    · exact continuousOn_const.add
        (contOn_prim L ((pinv_loc L).mul_continuousOn h2 (I_lc L)) hc)
    · exact continuousOn_const.add
        (contOn_prim L (((coef_loc L z).mul_continuousOn h1 (I_lc L)).sub hg) hc)

end Picard

/-- Families `G z x` which, for `x ∈ I`, are polynomials in `z` with coefficients continuous
on `I`. -/
def IsPolyFam (L : SLData) (G : ℂ → ℝ → ℂ) : Prop :=
  ∃ l : List (ℕ × (ℝ → ℂ)), (∀ p ∈ l, ContinuousOn p.2 L.I) ∧
    ∀ z, ∀ x ∈ L.I, G z x = (l.map (fun p => z ^ p.1 * p.2 x)).sum

section PolyFam

variable (L : SLData)

theorem listsum_contOn (l : List (ℕ × (ℝ → ℂ))) (hl : ∀ p ∈ l, ContinuousOn p.2 L.I) (z : ℂ) :
    ContinuousOn (fun x => (l.map (fun p => z ^ p.1 * p.2 x)).sum) L.I := by
  induction l with
  | nil => simpa using continuousOn_const
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (continuousOn_const.mul (hl a (by simp))).add
      (ih (fun p hp => hl p (by simp [hp])))

theorem polyFam_congr {G H : ℂ → ℝ → ℂ} (hH : IsPolyFam L H)
    (h : ∀ z, ∀ x ∈ L.I, G z x = H z x) : IsPolyFam L G := by
  obtain ⟨l, hl, hrep⟩ := hH
  exact ⟨l, hl, fun z x hx => (h z x hx).trans (hrep z x hx)⟩

theorem polyFam_fun {u : ℝ → ℂ} (hu : ContinuousOn u L.I) : IsPolyFam L (fun _ x => u x) :=
  ⟨[(0, u)], by simpa using hu, fun z x _ => by simp⟩

theorem polyFam_const (a : ℂ) : IsPolyFam L (fun _ _ => a) :=
  polyFam_fun L (u := fun _ => a) continuousOn_const

theorem polyFam_add {G H : ℂ → ℝ → ℂ} (hG : IsPolyFam L G) (hH : IsPolyFam L H) :
    IsPolyFam L (fun z x => G z x + H z x) := by
  obtain ⟨l1, h1, r1⟩ := hG
  obtain ⟨l2, h2, r2⟩ := hH
  refine ⟨l1 ++ l2, fun p hp => ?_, fun z x hx => ?_⟩
  · rcases List.mem_append.mp hp with hp | hp
    · exact h1 p hp
    · exact h2 p hp
  · beta_reduce
    rw [List.map_append, List.sum_append, r1 z x hx, r2 z x hx]

theorem polyFam_cmul {G : ℂ → ℝ → ℂ} (a : ℂ) (hG : IsPolyFam L G) :
    IsPolyFam L (fun z x => a * G z x) := by
  obtain ⟨l, hl, r⟩ := hG
  refine ⟨l.map (fun p => (p.1, fun x => a * p.2 x)), fun p hp => ?_, fun z x hx => ?_⟩
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact continuousOn_const.mul (hl q hq)
  · beta_reduce
    rw [r z x hx, List.map_map, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro p _
    simp only [Function.comp]; ring

theorem polyFam_zmul {G : ℂ → ℝ → ℂ} (hG : IsPolyFam L G) :
    IsPolyFam L (fun z x => z * G z x) := by
  obtain ⟨l, hl, r⟩ := hG
  refine ⟨l.map (fun p => (p.1 + 1, p.2)), fun p hp => ?_, fun z x hx => ?_⟩
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact hl q hq
  · beta_reduce
    rw [r z x hx, List.map_map, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro p _
    simp only [Function.comp]; ring

theorem integral_listsum {h : ℝ → ℂ} (hh : LocallyIntegrableOn h L.I) {c x : ℝ} (hc : c ∈ L.I)
    (hx : x ∈ L.I) (z : ℂ) (l : List (ℕ × (ℝ → ℂ))) (hl : ∀ p ∈ l, ContinuousOn p.2 L.I) :
    ∫ t in c..x, h t * (l.map (fun p => z ^ p.1 * p.2 t)).sum =
      (l.map (fun p => z ^ p.1 * ∫ t in c..x, h t * p.2 t)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hl' : ∀ p ∈ l, ContinuousOn p.2 L.I := fun p hp => hl p (by simp [hp])
    have ha : ContinuousOn a.2 L.I := hl a (by simp)
    simp only [List.map_cons, List.sum_cons]
    have e : (fun t => h t * (z ^ a.1 * a.2 t + (l.map (fun p => z ^ p.1 * p.2 t)).sum)) =
        fun t => z ^ a.1 * (h t * a.2 t) + h t * (l.map (fun p => z ^ p.1 * p.2 t)).sum := by
      funext t; ring
    rw [e, intervalIntegral.integral_add, intervalIntegral.integral_const_mul, ih hl']
    · exact (ii_of_loc L (hh.mul_continuousOn ha (I_lc L)) hc hx).const_mul _
    · exact ii_of_loc L (hh.mul_continuousOn (listsum_contOn L l hl' z) (I_lc L)) hc hx

theorem polyFam_integral {h : ℝ → ℂ} (hh : LocallyIntegrableOn h L.I) {c : ℝ} (hc : c ∈ L.I)
    {G : ℂ → ℝ → ℂ} (hG : IsPolyFam L G) :
    IsPolyFam L (fun z x => ∫ t in c..x, h t * G z t) := by
  obtain ⟨l, hl, r⟩ := hG
  refine ⟨l.map (fun p => (p.1, fun x => ∫ t in c..x, h t * p.2 t)), fun p hp => ?_,
    fun z x hx => ?_⟩
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact contOn_prim L (hh.mul_continuousOn (hl q hq) (I_lc L)) hc
  · have e : ∫ t in c..x, h t * G z t =
        ∫ t in c..x, h t * (l.map (fun p => z ^ p.1 * p.2 t)).sum := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [r z t (uIcc_subset_I L hc hx ht)]
    beta_reduce
    rw [e, integral_listsum L hh hc hx z l hl, List.map_map]
    rfl

theorem polyFam_differentiable {G : ℂ → ℝ → ℂ} (hG : IsPolyFam L G) {x : ℝ} (hx : x ∈ L.I) :
    Differentiable ℂ (fun z => G z x) := by
  obtain ⟨l, -, r⟩ := hG
  have e : (fun z => G z x) = fun z => (l.map (fun p => z ^ p.1 * p.2 x)).sum := by
    funext z; exact r z x hx
  rw [e]
  clear e r
  induction l with
  | nil => simpa using differentiable_const (0 : ℂ)
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ((differentiable_id.pow a.1).mul (differentiable_const _)).add ih

end PolyFam

section PicPoly

variable (L : SLData) (g : ℝ → ℂ) (c : ℝ) (α β : ℂ)

theorem pic_poly (hg : LocallyIntegrableOn (fun x => (L.r x : ℂ) * g x) L.I) (hc : c ∈ L.I) :
    ∀ n, IsPolyFam L (fun z x => (pic L g c α β n z x).1) ∧
      IsPolyFam L (fun z x => (pic L g c α β n z x).2) := by
  intro n
  induction n with
  | zero => exact ⟨polyFam_const L α, polyFam_const L β⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · exact polyFam_add L (polyFam_const L α) (polyFam_integral L (pinv_loc L) hc h2)
    · have hA := polyFam_integral L (q_loc L) hc h1
      have hB := polyFam_cmul L (-1) (polyFam_zmul L (polyFam_integral L (r_loc' L) hc h1))
      have hC := polyFam_fun L (u := fun x => -∫ t in c..x, (L.r t : ℂ) * g t)
        (contOn_prim L hg hc).neg
      refine polyFam_congr L (polyFam_add L (polyFam_const L β)
        (polyFam_add L hA (polyFam_add L hB hC))) (fun z x hx => ?_)
      have hc1 := (pic_contOn L g c α β hg hc n z).1
      show β + ∫ t in c..x, (((L.q t : ℂ) - z * (L.r t : ℂ)) * (pic L g c α β n z t).1 -
          (L.r t : ℂ) * g t) = _
      have i1 := ii_of_loc L ((q_loc L).mul_continuousOn hc1 (I_lc L)) hc hx
      have i2 := ii_of_loc L ((r_loc' L).mul_continuousOn hc1 (I_lc L)) hc hx
      have i3 := ii_of_loc L hg hc hx
      have e : (fun t => ((L.q t : ℂ) - z * (L.r t : ℂ)) * (pic L g c α β n z t).1 -
          (L.r t : ℂ) * g t) = fun t => ((L.q t : ℂ) * (pic L g c α β n z t).1 -
          z * ((L.r t : ℂ) * (pic L g c α β n z t).1)) - (L.r t : ℂ) * g t := by
        funext t; ring
      rw [e, intervalIntegral.integral_sub (i1.sub (i2.const_mul z)) i3,
        intervalIntegral.integral_sub i1 (i2.const_mul z), intervalIntegral.integral_const_mul]
      ring

end PicPoly

theorem iiR (L : SLData) {h : ℝ → ℝ} (hh : LocallyIntegrableOn h L.I) {x y : ℝ}
    (hx : x ∈ L.I) (hy : y ∈ L.I) : IntervalIntegrable h volume x y := by
  rw [intervalIntegrable_iff]
  exact (hh.integrableOn_compact_subset (uIcc_subset_I L hx hy) isCompact_uIcc).mono_set
    uIoc_subset_uIcc

theorem locR_const_mul (L : SLData) {h : ℝ → ℝ} (hh : LocallyIntegrableOn h L.I) (a : ℝ) :
    LocallyIntegrableOn (fun t => a * h t) L.I :=
  hh.continuousOn_mul continuousOn_const (I_lc L)

theorem uIoc_mono_of_mem {c x t : ℝ} (ht : t ∈ uIcc c x) : Ι c t ⊆ Ι c x := by
  rcases le_total c x with h | h
  · rw [uIcc_of_le h] at ht
    rw [uIoc_of_le ht.1, uIoc_of_le h]
    exact Ioc_subset_Ioc_right ht.2
  · rw [uIcc_of_ge h] at ht
    rw [uIoc_of_ge ht.2, uIoc_of_ge h]
    exact Ioc_subset_Ioc_left ht.1

section Estimates

variable (L : SLData) (g : ℝ → ℂ) (c : ℝ) (α β : ℂ)

/-- The majorant of the coefficient matrix for `‖z‖ ≤ R`. -/
noncomputable def aR (R : ℝ) (t : ℝ) : ℝ := ‖pinv L t‖ + ‖(L.q t : ℂ)‖ + R * ‖(L.r t : ℂ)‖

/-- The majorant of the first Picard step. -/
noncomputable def bR (R : ℝ) (t : ℝ) : ℝ :=
  ‖β‖ * ‖pinv L t‖ + ‖α‖ * (‖(L.q t : ℂ)‖ + R * ‖(L.r t : ℂ)‖) + ‖(L.r t : ℂ) * g t‖

/-- Size of the `n`-th Picard increment. -/
noncomputable def δ (n : ℕ) (z : ℂ) (t : ℝ) : ℝ :=
  ‖(pic L g c α β (n + 1) z t).1 - (pic L g c α β n z t).1‖ +
    ‖(pic L g c α β (n + 1) z t).2 - (pic L g c α β n z t).2‖

theorem aR_nonneg {R : ℝ} (hR : 0 ≤ R) (t : ℝ) : 0 ≤ aR L R t := by
  unfold aR; positivity

theorem bR_nonneg {R : ℝ} (hR : 0 ≤ R) (t : ℝ) : 0 ≤ bR L g α β R t := by
  unfold bR; positivity

theorem aR_loc (R : ℝ) : LocallyIntegrableOn (aR L R) L.I :=
  (((pinv_loc L).norm).add ((q_loc L).norm)).add (locR_const_mul L (r_loc' L).norm R)

theorem bR_loc (hg : LocallyIntegrableOn (fun x => (L.r x : ℂ) * g x) L.I) (R : ℝ) :
    LocallyIntegrableOn (bR L g α β R) L.I :=
  ((locR_const_mul L (pinv_loc L).norm _).add
    (locR_const_mul L (((q_loc L).norm).add (locR_const_mul L (r_loc' L).norm R)) _)).add
    hg.norm

variable (hg : LocallyIntegrableOn (fun x => (L.r x : ℂ) * g x) L.I) (hc : c ∈ L.I)
include hg hc

theorem pic_diff1 (n : ℕ) (z : ℂ) {x : ℝ} (hx : x ∈ L.I) :
    (pic L g c α β (n + 2) z x).1 - (pic L g c α β (n + 1) z x).1 =
      ∫ t in c..x, pinv L t * ((pic L g c α β (n + 1) z t).2 - (pic L g c α β n z t).2) := by
  have h1 := (pic_contOn L g c α β hg hc (n + 1) z).2
  have h0 := (pic_contOn L g c α β hg hc n z).2
  have i1 := ii_of_loc L ((pinv_loc L).mul_continuousOn h1 (I_lc L)) hc hx
  have i0 := ii_of_loc L ((pinv_loc L).mul_continuousOn h0 (I_lc L)) hc hx
  have e : (fun t => pinv L t * ((pic L g c α β (n + 1) z t).2 - (pic L g c α β n z t).2)) =
      fun t => pinv L t * (pic L g c α β (n + 1) z t).2 - pinv L t * (pic L g c α β n z t).2 := by
    funext t; ring
  rw [e, intervalIntegral.integral_sub i1 i0]
  simp only [pic]
  ring

theorem pic_diff2 (n : ℕ) (z : ℂ) {x : ℝ} (hx : x ∈ L.I) :
    (pic L g c α β (n + 2) z x).2 - (pic L g c α β (n + 1) z x).2 =
      ∫ t in c..x, ((L.q t : ℂ) - z * (L.r t : ℂ)) *
        ((pic L g c α β (n + 1) z t).1 - (pic L g c α β n z t).1) := by
  have h1 := (pic_contOn L g c α β hg hc (n + 1) z).1
  have h0 := (pic_contOn L g c α β hg hc n z).1
  have i1 : IntervalIntegrable (fun t => ((L.q t : ℂ) - z * (L.r t : ℂ)) *
      (pic L g c α β (n + 1) z t).1 - (L.r t : ℂ) * g t) volume c x :=
    ii_of_loc L (((coef_loc L z).mul_continuousOn h1 (I_lc L)).sub hg) hc hx
  have i0 : IntervalIntegrable (fun t => ((L.q t : ℂ) - z * (L.r t : ℂ)) *
      (pic L g c α β n z t).1 - (L.r t : ℂ) * g t) volume c x :=
    ii_of_loc L (((coef_loc L z).mul_continuousOn h0 (I_lc L)).sub hg) hc hx
  have e : (fun t => ((L.q t : ℂ) - z * (L.r t : ℂ)) *
        ((pic L g c α β (n + 1) z t).1 - (pic L g c α β n z t).1)) =
      fun t => (((L.q t : ℂ) - z * (L.r t : ℂ)) * (pic L g c α β (n + 1) z t).1 -
        (L.r t : ℂ) * g t) - (((L.q t : ℂ) - z * (L.r t : ℂ)) * (pic L g c α β n z t).1 -
        (L.r t : ℂ) * g t) := by
    funext t; ring
  rw [e, intervalIntegral.integral_sub i1 i0]
  simp only [pic]
  ring

theorem norm_coef_le {R : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R) (t : ℝ) :
    ‖(L.q t : ℂ) - z * (L.r t : ℂ)‖ ≤ ‖(L.q t : ℂ)‖ + R * ‖(L.r t : ℂ)‖ := by
  calc ‖(L.q t : ℂ) - z * (L.r t : ℂ)‖ ≤ ‖(L.q t : ℂ)‖ + ‖z * (L.r t : ℂ)‖ := norm_sub_le _ _
    _ ≤ ‖(L.q t : ℂ)‖ + R * ‖(L.r t : ℂ)‖ := by
      rw [norm_mul]; gcongr

theorem δ_contOn (n : ℕ) (z : ℂ) : ContinuousOn (δ L g c α β n z) L.I := by
  have a1 := pic_contOn L g c α β hg hc (n + 1) z
  have a0 := pic_contOn L g c α β hg hc n z
  exact ((a1.1.sub a0.1).norm).add ((a1.2.sub a0.2).norm)

theorem δ_step {R : ℝ} (hR : 0 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) (n : ℕ) {x : ℝ} (hx : x ∈ L.I) :
    δ L g c α β (n + 1) z x ≤ ∫ t in Ι c x, aR L R t * δ L g c α β n z t := by
  have hd := δ_contOn L g c α β hg hc n z
  have a1 := pic_contOn L g c α β hg hc (n + 1) z
  have a0 := pic_contOn L g c α β hg hc n z
  have hIcc : uIcc c x ⊆ L.I := uIcc_subset_I L hc hx
  have i1 : IntegrableOn (fun t => ‖pinv L t *
      ((pic L g c α β (n + 1) z t).2 - (pic L g c α β n z t).2)‖) (Ι c x) :=
    (ii_of_loc L ((pinv_loc L).mul_continuousOn (a1.2.sub a0.2) (I_lc L)) hc hx).def'.norm
  have i2 : IntegrableOn (fun t => ‖((L.q t : ℂ) - z * (L.r t : ℂ)) *
      ((pic L g c α β (n + 1) z t).1 - (pic L g c α β n z t).1)‖) (Ι c x) :=
    (ii_of_loc L ((coef_loc L z).mul_continuousOn (a1.1.sub a0.1) (I_lc L)) hc hx).def'.norm
  have iC : IntegrableOn (fun t => aR L R t * δ L g c α β n z t) (Ι c x) :=
    (iiR L (aR_loc L R) hc hx).def'.mul_continuousOn_of_subset (hd.mono hIcc)
      measurableSet_uIoc isCompact_uIcc uIoc_subset_uIcc
  have e1 := pic_diff1 L g c α β hg hc n z hx
  have e2 := pic_diff2 L g c α β hg hc n z hx
  unfold δ
  rw [e1, e2]
  calc _ ≤ (∫ t in Ι c x, ‖pinv L t *
          ((pic L g c α β (n + 1) z t).2 - (pic L g c α β n z t).2)‖) +
        ∫ t in Ι c x, ‖((L.q t : ℂ) - z * (L.r t : ℂ)) *
          ((pic L g c α β (n + 1) z t).1 - (pic L g c α β n z t).1)‖ :=
        add_le_add (intervalIntegral.norm_integral_le_integral_norm_uIoc)
          (intervalIntegral.norm_integral_le_integral_norm_uIoc)
    _ = ∫ t in Ι c x, (‖pinv L t *
          ((pic L g c α β (n + 1) z t).2 - (pic L g c α β n z t).2)‖ +
        ‖((L.q t : ℂ) - z * (L.r t : ℂ)) *
          ((pic L g c α β (n + 1) z t).1 - (pic L g c α β n z t).1)‖) :=
        (integral_add i1 i2).symm
    _ ≤ ∫ t in Ι c x, aR L R t * δ L g c α β n z t := by
        refine setIntegral_mono_on (i1.add i2) iC measurableSet_uIoc (fun t _ => ?_)
        unfold aR δ
        rw [norm_mul, norm_mul]
        have hco := norm_coef_le L g c hg hc hz t
        have h1 := norm_nonneg ((pic L g c α β (n + 1) z t).1 - (pic L g c α β n z t).1)
        have h2 := norm_nonneg ((pic L g c α β (n + 1) z t).2 - (pic L g c α β n z t).2)
        have h3 := norm_nonneg (pinv L t)
        have h4 : 0 ≤ ‖(L.q t : ℂ)‖ + R * ‖(L.r t : ℂ)‖ := by positivity
        nlinarith

theorem δ_zero {R : ℝ} (hR : 0 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) {x : ℝ} (hx : x ∈ L.I) :
    ∀ t ∈ uIcc c x, δ L g c α β 0 z t ≤ ∫ s in Ι c x, bR L g α β R s := by
  intro t ht
  have htI : t ∈ L.I := uIcc_subset_I L hc hx ht
  have hIoc : Ι c t ⊆ Ι c x := uIoc_mono_of_mem ht
  have ib : IntegrableOn (bR L g α β R) (Ι c x) := (iiR L (bR_loc L g α β hg R) hc hx).def'
  have ibt : IntegrableOn (bR L g α β R) (Ι c t) := (iiR L (bR_loc L g α β hg R) hc htI).def'
  have i1 : IntegrableOn (fun s => ‖pinv L s * β‖) (Ι c t) :=
    (ii_of_loc L ((pinv_loc L).mul_continuousOn continuousOn_const (I_lc L)) hc htI).def'.norm
  have i2 : IntegrableOn (fun s => ‖((L.q s : ℂ) - z * (L.r s : ℂ)) * α - (L.r s : ℂ) * g s‖)
      (Ι c t) :=
    (ii_of_loc L (((coef_loc L z).mul_continuousOn continuousOn_const (I_lc L)).sub hg)
      hc htI).def'.norm
  have e : δ L g c α β 0 z t = ‖∫ s in c..t, pinv L s * β‖ +
      ‖∫ s in c..t, (((L.q s : ℂ) - z * (L.r s : ℂ)) * α - (L.r s : ℂ) * g s)‖ := by
    unfold δ; simp only [pic, add_sub_cancel_left]
  rw [e]
  calc _ ≤ (∫ s in Ι c t, ‖pinv L s * β‖) +
        ∫ s in Ι c t, ‖((L.q s : ℂ) - z * (L.r s : ℂ)) * α - (L.r s : ℂ) * g s‖ :=
        add_le_add (intervalIntegral.norm_integral_le_integral_norm_uIoc)
          (intervalIntegral.norm_integral_le_integral_norm_uIoc)
    _ = ∫ s in Ι c t, (‖pinv L s * β‖ +
        ‖((L.q s : ℂ) - z * (L.r s : ℂ)) * α - (L.r s : ℂ) * g s‖) := (integral_add i1 i2).symm
    _ ≤ ∫ s in Ι c t, bR L g α β R s := by
        refine setIntegral_mono_on (i1.add i2) ibt measurableSet_uIoc (fun s _ => ?_)
        unfold bR
        have hco := norm_coef_le L g c hg hc hz s
        have h5 : ‖((L.q s : ℂ) - z * (L.r s : ℂ)) * α - (L.r s : ℂ) * g s‖ ≤
            ‖(L.q s : ℂ) - z * (L.r s : ℂ)‖ * ‖α‖ + ‖(L.r s : ℂ) * g s‖ := by
          calc _ ≤ ‖((L.q s : ℂ) - z * (L.r s : ℂ)) * α‖ + ‖(L.r s : ℂ) * g s‖ := norm_sub_le _ _
            _ = _ := by rw [norm_mul]
        rw [norm_mul]
        have h6 := norm_nonneg α
        nlinarith
    _ ≤ ∫ s in Ι c x, bR L g α β R s :=
        setIntegral_mono_set ib (Eventually.of_forall (fun s => bR_nonneg L g α β hR s))
          (Eventually.of_forall hIoc)

theorem δ_bound {R : ℝ} (hR : 0 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) {x : ℝ} (hx : x ∈ L.I) :
    ∀ n, ∀ t ∈ uIcc c x, δ L g c α β n z t ≤
      (∫ s in Ι c x, bR L g α β R s) * (∫ s in Ι c x, aR L R s) ^ n / n.factorial := by
  intro n t ht
  have hIcc := uIcc_subset_I L hc hx
  have hb := iter_bound (aR_nonneg L hR) (iiR L (aR_loc L R) hc hx)
    (fun n => δ L g c α β n z) (fun n => (δ_contOn L g c α β hg hc n z).mono hIcc)
    (δ_zero L g c α β hg hc hR hz hx)
    (fun n t ht => δ_step L g c α β hg hc hR hz n (hIcc ht)) n t ht
  refine hb.trans ?_
  have hK : (∫ s in Ι c t, aR L R s) ≤ ∫ s in Ι c x, aR L R s :=
    setIntegral_mono_set (iiR L (aR_loc L R) hc hx).def'
      (Eventually.of_forall (fun s => aR_nonneg L hR s))
      (Eventually.of_forall (uIoc_mono_of_mem ht))
  have hK0 : 0 ≤ ∫ s in Ι c t, aR L R s :=
    setIntegral_nonneg measurableSet_uIoc (fun s _ => aR_nonneg L hR s)
  have hB0 : 0 ≤ ∫ s in Ι c x, bR L g α β R s :=
    setIntegral_nonneg measurableSet_uIoc (fun s _ => bR_nonneg L g α β hR s)
  gcongr

end Estimates

end IvpAux


open MeasureTheory Set Filter Topology
open scoped Interval

namespace IvpAux

open TeschlQM.SturmLiouville VoCAux LagAux

theorem contOn_I_of (L : SLData) {f : ℝ → ℂ}
    (h : ∀ s ∈ L.I, ∀ t ∈ L.I, ContinuousOn f (uIcc s t)) : ContinuousOn f L.I := by
  intro x hx
  obtain ⟨s, t, hsx, hxt, hs, ht⟩ := exists_Icc_subset_I L hx
  have hnhds : uIcc s t ∈ 𝓝 x := by
    rw [uIcc_of_le (hsx.trans hxt).le]; exact Icc_mem_nhds hsx hxt
  exact ((h s hs t ht).continuousAt hnhds).continuousWithinAt

theorem lim_integral {A : ℝ → ℂ} {c x : ℝ} (hA : IntervalIntegrable A volume c x)
    {G : ℕ → ℝ → ℂ} {H : ℝ → ℂ} (M : ℝ) (hG : ∀ n, ContinuousOn (G n) (uIcc c x))
    (hb : ∀ n, ∀ t ∈ uIcc c x, ‖G n t‖ ≤ M)
    (hlim : ∀ t ∈ uIcc c x, Tendsto (fun n => G n t) atTop (𝓝 (H t))) :
    Tendsto (fun n => ∫ t in c..x, A t * G n t) atTop (𝓝 (∫ t in c..x, A t * H t)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun t => ‖A t‖ * M) (Eventually.of_forall (fun n => ?_))
    (Eventually.of_forall (fun n => Eventually.of_forall (fun t ht => ?_)))
    (hA.norm.mul_const M) (Eventually.of_forall (fun t ht => ?_))
  · exact (hA.def'.mul_continuousOn_of_subset (hG n) measurableSet_uIoc isCompact_uIcc
      uIoc_subset_uIcc).aestronglyMeasurable
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb n t (uIoc_subset_uIcc ht)) (norm_nonneg _)
  · exact (hlim t (uIoc_subset_uIcc ht)).const_mul (A t)

section Conv

variable (L : SLData) (g : ℝ → ℂ) (c : ℝ) (α β : ℂ)

noncomputable def D1 (n : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  (pic L g c α β (n + 1) z t).1 - (pic L g c α β n z t).1

noncomputable def D2 (n : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  (pic L g c α β (n + 1) z t).2 - (pic L g c α β n z t).2

/-- The solution. -/
noncomputable def solF (z : ℂ) (x : ℝ) : ℂ := α + ∑' n, D1 L g c α β n z x

/-- Its quasi-derivative. -/
noncomputable def solW (z : ℂ) (x : ℝ) : ℂ := β + ∑' n, D2 L g c α β n z x

theorem D1_le (n : ℕ) (z : ℂ) (t : ℝ) : ‖D1 L g c α β n z t‖ ≤ δ L g c α β n z t := by
  unfold D1 δ; exact le_add_of_nonneg_right (norm_nonneg _)

theorem D2_le (n : ℕ) (z : ℂ) (t : ℝ) : ‖D2 L g c α β n z t‖ ≤ δ L g c α β n z t := by
  unfold D2 δ; exact le_add_of_nonneg_left (norm_nonneg _)

theorem sum_D1 (N : ℕ) (z : ℂ) (t : ℝ) :
    ∑ n ∈ Finset.range N, D1 L g c α β n z t = (pic L g c α β N z t).1 - α := by
  unfold D1
  rw [Finset.sum_range_sub (fun n => (pic L g c α β n z t).1)]
  rfl

theorem sum_D2 (N : ℕ) (z : ℂ) (t : ℝ) :
    ∑ n ∈ Finset.range N, D2 L g c α β n z t = (pic L g c α β N z t).2 - β := by
  unfold D2
  rw [Finset.sum_range_sub (fun n => (pic L g c α β n z t).2)]
  rfl

variable (hg : LocallyIntegrableOn (fun x => (L.r x : ℂ) * g x) L.I) (hc : c ∈ L.I)
include hg hc

theorem unif_bound {R : ℝ} (hR : 0 ≤ R) {s t : ℝ} (hs : s ∈ L.I) (ht : t ∈ L.I) :
    ∃ C : ℕ → ℝ, Summable C ∧ (∀ n, 0 ≤ C n) ∧
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ n, ∀ u ∈ uIcc s t, δ L g c α β n z u ≤ C n := by
  set Bs := ∫ v in Ι c s, bR L g α β R v
  set Ks := ∫ v in Ι c s, aR L R v
  set Bt := ∫ v in Ι c t, bR L g α β R v
  set Kt := ∫ v in Ι c t, aR L R v
  have hBs : 0 ≤ Bs := setIntegral_nonneg measurableSet_uIoc (fun v _ => bR_nonneg L g α β hR v)
  have hBt : 0 ≤ Bt := setIntegral_nonneg measurableSet_uIoc (fun v _ => bR_nonneg L g α β hR v)
  have hKs : 0 ≤ Ks := setIntegral_nonneg measurableSet_uIoc (fun v _ => aR_nonneg L hR v)
  have hKt : 0 ≤ Kt := setIntegral_nonneg measurableSet_uIoc (fun v _ => aR_nonneg L hR v)
  refine ⟨fun n => Bs * (Ks ^ n / n.factorial) + Bt * (Kt ^ n / n.factorial), ?_, ?_, ?_⟩
  · exact ((Real.summable_pow_div_factorial Ks).mul_left Bs).add
      ((Real.summable_pow_div_factorial Kt).mul_left Bt)
  · intro n; positivity
  · intro z hz n u hu
    have h0 : 0 ≤ Bs * (Ks ^ n / n.factorial) := by positivity
    have h1 : 0 ≤ Bt * (Kt ^ n / n.factorial) := by positivity
    rcases uIcc_subset_uIcc_union_uIcc (b := c) hu with h | h
    · rw [uIcc_comm] at h
      have := δ_bound L g c α β hg hc hR hz hs n u h
      rw [mul_div_assoc] at this
      linarith
    · have := δ_bound L g c α β hg hc hR hz ht n u h
      rw [mul_div_assoc] at this
      linarith

theorem tendsto_pic1 (z : ℂ) {x : ℝ} (hx : x ∈ L.I) :
    Tendsto (fun N => (pic L g c α β N z x).1) atTop (𝓝 (solF L g c α β z x)) := by
  obtain ⟨C, hC, -, hb⟩ := unif_bound L g c α β hg hc (norm_nonneg z) hx hx
  have hs : Summable (fun n => D1 L g c α β n z x) :=
    hC.of_norm_bounded (fun n => (D1_le L g c α β n z x).trans (hb z le_rfl n x left_mem_uIcc))
  have := (hs.hasSum.tendsto_sum_nat).const_add α
  simp only [sum_D1, add_sub_cancel] at this
  exact this

theorem tendsto_pic2 (z : ℂ) {x : ℝ} (hx : x ∈ L.I) :
    Tendsto (fun N => (pic L g c α β N z x).2) atTop (𝓝 (solW L g c α β z x)) := by
  obtain ⟨C, hC, -, hb⟩ := unif_bound L g c α β hg hc (norm_nonneg z) hx hx
  have hs : Summable (fun n => D2 L g c α β n z x) :=
    hC.of_norm_bounded (fun n => (D2_le L g c α β n z x).trans (hb z le_rfl n x left_mem_uIcc))
  have := (hs.hasSum.tendsto_sum_nat).const_add β
  simp only [sum_D2, add_sub_cancel] at this
  exact this

theorem D1_contOn (n : ℕ) (z : ℂ) : ContinuousOn (D1 L g c α β n z) L.I :=
  (pic_contOn L g c α β hg hc (n + 1) z).1.sub (pic_contOn L g c α β hg hc n z).1

theorem D2_contOn (n : ℕ) (z : ℂ) : ContinuousOn (D2 L g c α β n z) L.I :=
  (pic_contOn L g c α β hg hc (n + 1) z).2.sub (pic_contOn L g c α β hg hc n z).2

theorem solF_contOn (z : ℂ) : ContinuousOn (solF L g c α β z) L.I := by
  refine contOn_I_of L (fun s hs t ht => ?_)
  obtain ⟨C, hC, -, hb⟩ := unif_bound L g c α β hg hc (norm_nonneg z) hs ht
  exact continuousOn_const.add (continuousOn_tsum
    (fun n => (D1_contOn L g c α β hg hc n z).mono (uIcc_subset_I L hs ht)) hC
    (fun n u hu => (D1_le L g c α β n z u).trans (hb z le_rfl n u hu)))

theorem solW_contOn (z : ℂ) : ContinuousOn (solW L g c α β z) L.I := by
  refine contOn_I_of L (fun s hs t ht => ?_)
  obtain ⟨C, hC, -, hb⟩ := unif_bound L g c α β hg hc (norm_nonneg z) hs ht
  exact continuousOn_const.add (continuousOn_tsum
    (fun n => (D2_contOn L g c α β hg hc n z).mono (uIcc_subset_I L hs ht)) hC
    (fun n u hu => (D2_le L g c α β n z u).trans (hb z le_rfl n u hu)))

/-- Uniform bound on the Picard iterates. -/
theorem pic_bound (z : ℂ) {x : ℝ} (hx : x ∈ L.I) :
    ∃ M : ℝ, ∀ n, ∀ t ∈ uIcc c x,
      ‖(pic L g c α β n z t).1‖ ≤ M ∧ ‖(pic L g c α β n z t).2‖ ≤ M := by
  obtain ⟨C, hC, hC0, hb⟩ := unif_bound L g c α β hg hc (norm_nonneg z) hc hx
  refine ⟨‖α‖ + ‖β‖ + ∑' n, C n, fun N t ht => ⟨?_, ?_⟩⟩
  · have e : (pic L g c α β N z t).1 = α + ∑ n ∈ Finset.range N, D1 L g c α β n z t := by
      rw [sum_D1]; ring
    rw [e]
    calc _ ≤ ‖α‖ + ‖∑ n ∈ Finset.range N, D1 L g c α β n z t‖ := norm_add_le _ _
      _ ≤ ‖α‖ + ∑ n ∈ Finset.range N, C n := by
          gcongr
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n _ =>
            (D1_le L g c α β n z t).trans (hb z le_rfl n t ht)))
      _ ≤ ‖α‖ + ‖β‖ + ∑' n, C n := by
          have := hC.sum_le_tsum (Finset.range N) (fun n _ => hC0 n)
          have := norm_nonneg β
          linarith
  · have e : (pic L g c α β N z t).2 = β + ∑ n ∈ Finset.range N, D2 L g c α β n z t := by
      rw [sum_D2]; ring
    rw [e]
    calc _ ≤ ‖β‖ + ‖∑ n ∈ Finset.range N, D2 L g c α β n z t‖ := norm_add_le _ _
      _ ≤ ‖β‖ + ∑ n ∈ Finset.range N, C n := by
          gcongr
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n _ =>
            (D2_le L g c α β n z t).trans (hb z le_rfl n t ht)))
      _ ≤ ‖α‖ + ‖β‖ + ∑' n, C n := by
          have := hC.sum_le_tsum (Finset.range N) (fun n _ => hC0 n)
          have := norm_nonneg α
          linarith

theorem solF_eq (z : ℂ) {x : ℝ} (hx : x ∈ L.I) :
    solF L g c α β z x = α + ∫ t in c..x, pinv L t * solW L g c α β z t := by
  have hIcc := uIcc_subset_I L hc hx
  obtain ⟨M, hM⟩ := pic_bound L g c α β hg hc z hx
  have h1 := (tendsto_pic1 L g c α β hg hc z hx).comp (tendsto_add_atTop_nat 1)
  have h2 := (lim_integral (G := fun n t => (pic L g c α β n z t).2)
    (H := solW L g c α β z) (ii_of_loc L (pinv_loc L) hc hx) M
    (fun n => (pic_contOn L g c α β hg hc n z).2.mono hIcc) (fun n t ht => (hM n t ht).2)
    (fun t ht => tendsto_pic2 L g c α β hg hc z (hIcc ht))).const_add α
  exact tendsto_nhds_unique h1 h2

theorem solW_eq (z : ℂ) {x : ℝ} (hx : x ∈ L.I) :
    solW L g c α β z x = β + ∫ t in c..x, (((L.q t : ℂ) - z * (L.r t : ℂ)) *
      solF L g c α β z t - (L.r t : ℂ) * g t) := by
  have hIcc := uIcc_subset_I L hc hx
  obtain ⟨M, hM⟩ := pic_bound L g c α β hg hc z hx
  have hA := ii_of_loc L (coef_loc L z) hc hx
  have hrg := ii_of_loc L hg hc hx
  have h1 := (tendsto_pic2 L g c α β hg hc z hx).comp (tendsto_add_atTop_nat 1)
  have h2 := ((lim_integral (G := fun n t => (pic L g c α β n z t).1)
    (H := solF L g c α β z) hA M
    (fun n => (pic_contOn L g c α β hg hc n z).1.mono hIcc) (fun n t ht => (hM n t ht).1)
    (fun t ht => tendsto_pic1 L g c α β hg hc z (hIcc ht))).sub_const
    (∫ t in c..x, (L.r t : ℂ) * g t)).const_add β
  have hF := solF_contOn L g c α β hg hc z
  rw [intervalIntegral.integral_sub
    (ii_of_loc L ((coef_loc L z).mul_continuousOn hF (I_lc L)) hc hx) hrg]
  refine tendsto_nhds_unique h1 (h2.congr (fun n => ?_))
  have hn := (pic_contOn L g c α β hg hc n z).1
  show β + ((∫ t in c..x, ((L.q t : ℂ) - z * (L.r t : ℂ)) * (pic L g c α β n z t).1) -
    ∫ t in c..x, (L.r t : ℂ) * g t) = _
  simp only [Function.comp, pic]
  rw [intervalIntegral.integral_sub
    (ii_of_loc L ((coef_loc L z).mul_continuousOn hn (I_lc L)) hc hx) hrg]

end Conv

end IvpAux


open MeasureTheory Set Filter Topology
open scoped Interval

namespace IvpAux

open TeschlQM.SturmLiouville VoCAux LagAux

section Final

variable (L : SLData) (g : ℝ → ℂ) (c : ℝ) (α β : ℂ)
variable (hg : LocallyIntegrableOn (fun x => (L.r x : ℂ) * g x) L.I) (hc : c ∈ L.I)
include hg hc

theorem diff_of_eq {F h : ℝ → ℂ} {a : ℂ} (hh : LocallyIntegrableOn h L.I)
    (hF : ∀ x ∈ L.I, F x = a + ∫ t in c..x, h t) :
    ∀ x ∈ L.I, ∀ y ∈ L.I, F y - F x = ∫ t in x..y, h t := by
  intro x hx y hy
  rw [hF x hx, hF y hy, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (ii_of_loc L hh hc hy) (ii_of_loc L hh hc hx)]

theorem sol_isQD (z : ℂ) :
    IsQuasiDerivative L (solF L g c α β z) (solW L g c α β z) := by
  have hF := solF_contOn L g c α β hg hc z
  have hW := solW_contOn L g c α β hg hc z
  have h1 : LocallyIntegrableOn (fun t => ((L.q t : ℂ) - z * (L.r t : ℂ)) *
      solF L g c α β z t - (L.r t : ℂ) * g t) L.I :=
    ((coef_loc L z).mul_continuousOn hF (I_lc L)).sub hg
  have h2 : LocallyIntegrableOn (fun t => pinv L t * solW L g c α β z t) L.I :=
    (pinv_loc L).mul_continuousOn hW (I_lc L)
  have e : (fun t => solW L g c α β z t / (L.p t : ℂ)) =
      fun t => pinv L t * solW L g c α β z t := by
    funext t; exact div_p L _ t
  refine ⟨⟨_, h1, diff_of_eq L g c hg hc h1 (fun x hx => solW_eq L g c α β hg hc z hx)⟩,
    ?_, ?_⟩
  · rw [e]; exact h2
  · rw [e]; exact diff_of_eq L g c hg hc h2 (fun x hx => solF_eq L g c α β hg hc z hx)

theorem qd_solF (z : ℂ) : ∀ x ∈ L.I, quasiDeriv L (solF L g c α β z) x = solW L g c α β z x :=
  qd_unique L (isQD_quasiDeriv L (sol_isQD L g c α β hg hc z)) (sol_isQD L g c α β hg hc z)

theorem sol_isSolution (z : ℂ) : IsSolution L z g (solF L g c α β z) := by
  have hF := solF_contOn L g c α β hg hc z
  have e : (fun t => (L.q t : ℂ) * solF L g c α β z t -
      (L.r t : ℂ) * (z * solF L g c α β z t + g t)) =
      fun t => ((L.q t : ℂ) - z * (L.r t : ℂ)) * solF L g c α β z t - (L.r t : ℂ) * g t := by
    funext t; ring
  have h1 : LocallyIntegrableOn (fun t => ((L.q t : ℂ) - z * (L.r t : ℂ)) *
      solF L g c α β z t - (L.r t : ℂ) * g t) L.I :=
    ((coef_loc L z).mul_continuousOn hF (I_lc L)).sub hg
  refine ⟨isQD_quasiDeriv L (sol_isQD L g c α β hg hc z), ?_, fun x hx y hy => ?_⟩
  · show LocallyIntegrableOn (fun t => (L.q t : ℂ) * solF L g c α β z t -
      (L.r t : ℂ) * (z * solF L g c α β z t + g t)) L.I
    rw [e]; exact h1
  · show _ = ∫ t in x..y, ((L.q t : ℂ) * solF L g c α β z t -
      (L.r t : ℂ) * (z * solF L g c α β z t + g t))
    rw [e, qd_solF L g c α β hg hc z x hx, qd_solF L g c α β hg hc z y hy]
    exact diff_of_eq L g c hg hc h1 (fun x hx => solW_eq L g c α β hg hc z hx) x hx y hy

theorem solF_c (z : ℂ) : solF L g c α β z c = α := by
  rw [solF_eq L g c α β hg hc z hc]; simp

theorem qd_solF_c (z : ℂ) : quasiDeriv L (solF L g c α β z) c = β := by
  rw [qd_solF L g c α β hg hc z c hc, solW_eq L g c α β hg hc z hc]; simp

theorem solF_differentiable {x : ℝ} (hx : x ∈ L.I) :
    Differentiable ℂ (fun z => solF L g c α β z x) := by
  intro z0
  set R := ‖z0‖ + 1
  have hR : 0 ≤ R := by positivity
  obtain ⟨C, hC, -, hb⟩ := unif_bound L g c α β hg hc hR hx hx
  have hd : DifferentiableOn ℂ (fun w => ∑' n, D1 L g c α β n w x) (Metric.ball 0 R) := by
    refine Complex.differentiableOn_tsum_of_summable_norm hC (fun n => ?_) Metric.isOpen_ball
      (fun n w hw => (D1_le L g c α β n w x).trans (hb w ?_ n x left_mem_uIcc))
    · have p1 := polyFam_differentiable L (pic_poly L g c α β hg hc (n + 1)).1 hx
      have p0 := polyFam_differentiable L (pic_poly L g c α β hg hc n).1 hx
      exact (p1.sub p0).differentiableOn
    · rw [Metric.mem_ball, dist_zero_right] at hw; exact hw.le
  have hz0 : Metric.ball (0 : ℂ) R ∈ 𝓝 z0 :=
    Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_zero_right]; linarith)
  exact ((hd.differentiableAt hz0).const_add α)

theorem sol_unique (z : ℂ) (f : ℝ → ℂ) (hf : IsSolution L z g f) (hfc : f c = α)
    (hf1c : quasiDeriv L f c = β) : ∀ x ∈ L.I, f x = solF L g c α β z x := by
  intro x hx
  obtain ⟨⟨hac, hloc, hprim⟩, hloc2, hprim2⟩ := hf
  set f1 := quasiDeriv L f
  set F := solF L g c α β z
  set W := solW L g c α β z
  set R := ‖z‖
  have hR : 0 ≤ R := norm_nonneg z
  have hIcc := uIcc_subset_I L hc hx
  have hFc := solF_contOn L g c α β hg hc z
  have hWc := solW_contOn L g c α β hg hc z
  have hf1c' : ContinuousOn f1 (uIcc c x) := continuousOn_of_ACloc L hac hc hx
  have hfeq : ∀ t ∈ L.I, f t = α + ∫ s in c..t, pinv L s * f1 s := by
    intro t ht
    have := hprim c hc t ht
    simp only [div_p] at this
    rw [← hfc, ← this]; ring
  have hf1eq : ∀ t ∈ L.I, f1 t = β + ∫ s in c..t, (((L.q s : ℂ) - z * (L.r s : ℂ)) * f s -
      (L.r s : ℂ) * g s) := by
    intro t ht
    have := hprim2 c hc t ht
    have e : (fun s => (L.q s : ℂ) * f s - (L.r s : ℂ) * (z * f s + g s)) =
        fun s => ((L.q s : ℂ) - z * (L.r s : ℂ)) * f s - (L.r s : ℂ) * g s := by
      funext s; ring
    rw [e] at this
    rw [← hf1c, ← this]; ring
  have hl : LocallyIntegrableOn (fun s => pinv L s * f1 s) L.I := by
    have e : (fun s => pinv L s * f1 s) = fun s => f1 s / (L.p s : ℂ) := by
      funext s; rw [div_p]
    rw [e]; exact hloc
  have hl2 : LocallyIntegrableOn (fun s => ((L.q s : ℂ) - z * (L.r s : ℂ)) * f s -
      (L.r s : ℂ) * g s) L.I := by
    have e : (fun s => ((L.q s : ℂ) - z * (L.r s : ℂ)) * f s - (L.r s : ℂ) * g s) =
        fun s => (L.q s : ℂ) * f s - (L.r s : ℂ) * (z * f s + g s) := by
      funext s; ring
    rw [e]; exact hloc2
  have hfcont : ContinuousOn f (uIcc c x) := by
    exact continuousOn_of_primitive (ii_of_loc L hl hc hx) (fun t ht => by
      rw [hfeq t (hIcc ht), hfeq c hc]; simp)
  set φ : ℝ → ℝ := fun t => ‖f t - F t‖ + ‖f1 t - W t‖
  have hφc : ContinuousOn φ (uIcc c x) :=
    ((hfcont.sub (hFc.mono hIcc)).norm).add ((hf1c'.sub (hWc.mono hIcc)).norm)
  obtain ⟨M, hM⟩ := isCompact_uIcc.exists_bound_of_continuousOn hφc
  have hstep : ∀ t ∈ uIcc c x, φ t ≤ ∫ s in Ι c t, aR L R s * φ s := by
    intro t ht
    have htI := hIcc ht
    have hsub : uIcc c t ⊆ uIcc c x := uIcc_subset_uIcc left_mem_uIcc ht
    have hfc' := hfcont.mono hsub
    have hf1' := hf1c'.mono hsub
    have hF' := (hFc.mono hIcc).mono hsub
    have hW' := (hWc.mono hIcc).mono hsub
    have i1 : IntegrableOn (fun s => ‖pinv L s * (f1 s - W s)‖) (Ι c t) :=
      ((iiR L (pinv_loc L).norm hc htI).def'.mul_continuousOn_of_subset
        ((hf1'.sub hW').norm) measurableSet_uIoc isCompact_uIcc uIoc_subset_uIcc).congr
        (Eventually.of_forall (fun s => (norm_mul _ _).symm))
    have i2 : IntegrableOn (fun s => ‖((L.q s : ℂ) - z * (L.r s : ℂ)) * (f s - F s)‖)
        (Ι c t) :=
      ((iiR L (coef_loc L z).norm hc htI).def'.mul_continuousOn_of_subset
        ((hfc'.sub hF').norm) measurableSet_uIoc isCompact_uIcc uIoc_subset_uIcc).congr
        (Eventually.of_forall (fun s => (norm_mul _ _).symm))
    have iC : IntegrableOn (fun s => aR L R s * φ s) (Ι c t) :=
      (iiR L (aR_loc L R) hc htI).def'.mul_continuousOn_of_subset (hφc.mono hsub)
        measurableSet_uIoc isCompact_uIcc uIoc_subset_uIcc
    have e1 : f t - F t = ∫ s in c..t, pinv L s * (f1 s - W s) := by
      have eF : F t = α + ∫ s in c..t, pinv L s * W s := solF_eq L g c α β hg hc z htI
      rw [hfeq t htI, eF, add_sub_add_left_eq_sub,
        ← intervalIntegral.integral_sub (ii_of_loc L hl hc htI)
          (ii_of_loc L ((pinv_loc L).mul_continuousOn hWc (I_lc L)) hc htI)]
      congr 1; funext s; ring
    have e2 : f1 t - W t = ∫ s in c..t, ((L.q s : ℂ) - z * (L.r s : ℂ)) * (f s - F s) := by
      have eW : W t = β + ∫ s in c..t, (((L.q s : ℂ) - z * (L.r s : ℂ)) * F s -
          (L.r s : ℂ) * g s) := solW_eq L g c α β hg hc z htI
      have j2 : IntervalIntegrable (fun s => ((L.q s : ℂ) - z * (L.r s : ℂ)) * F s -
          (L.r s : ℂ) * g s) volume c t :=
        ii_of_loc L (((coef_loc L z).mul_continuousOn hFc (I_lc L)).sub hg) hc htI
      rw [hf1eq t htI, eW, add_sub_add_left_eq_sub,
        ← intervalIntegral.integral_sub (ii_of_loc L hl2 hc htI) j2]
      congr 1; funext s; ring
    show ‖f t - F t‖ + ‖f1 t - W t‖ ≤ _
    rw [e1, e2]
    calc _ ≤ (∫ s in Ι c t, ‖pinv L s * (f1 s - W s)‖) +
          ∫ s in Ι c t, ‖((L.q s : ℂ) - z * (L.r s : ℂ)) * (f s - F s)‖ :=
          add_le_add (intervalIntegral.norm_integral_le_integral_norm_uIoc)
            (intervalIntegral.norm_integral_le_integral_norm_uIoc)
      _ = ∫ s in Ι c t, (‖pinv L s * (f1 s - W s)‖ +
          ‖((L.q s : ℂ) - z * (L.r s : ℂ)) * (f s - F s)‖) := (integral_add i1 i2).symm
      _ ≤ ∫ s in Ι c t, aR L R s * φ s := by
          refine setIntegral_mono_on (i1.add i2) iC measurableSet_uIoc (fun s _ => ?_)
          unfold aR
          show _ ≤ _ * (‖f s - F s‖ + ‖f1 s - W s‖)
          rw [norm_mul, norm_mul]
          have hco := norm_coef_le L g c hg hc (le_refl ‖z‖) s
          have h1 := norm_nonneg (f s - F s)
          have h2 := norm_nonneg (f1 s - W s)
          have h3 := norm_nonneg (pinv L s)
          have h4 : 0 ≤ ‖(L.q s : ℂ)‖ + R * ‖(L.r s : ℂ)‖ := by positivity
          nlinarith
  have hb := iter_bound (aR_nonneg L hR) (iiR L (aR_loc L R) hc hx) (fun _ => φ)
    (fun _ => hφc) (fun t ht => (le_abs_self _).trans (by simpa using hM t ht))
    (fun _ t ht => hstep t ht)
  have hlim : Tendsto (fun n => M * (∫ s in Ι c x, aR L R s) ^ n / n.factorial) atTop (𝓝 0) := by
    have := ((Real.summable_pow_div_factorial (∫ s in Ι c x, aR L R s)).tendsto_atTop_zero).const_mul M
    simp only [mul_zero] at this
    refine this.congr (fun n => ?_)
    ring
  have hφx : φ x ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall (fun n => hb n x right_mem_uIcc))
  have h0 : ‖f x - F x‖ = 0 := le_antisymm (by
    have := norm_nonneg (f1 x - W x); show ‖f x - F x‖ ≤ 0; linarith) (norm_nonneg _)
  rw [norm_eq_zero, sub_eq_zero] at h0
  exact h0

end Final

end IvpAux

open TeschlQM.SturmLiouville MeasureTheory

theorem IvpAux.ivp (L : SLData) (g : ℝ → ℂ)
    (hg : LocallyIntegrableOn (fun x => (L.r x : ℂ) * g x) L.I)
    (c : ℝ) (hc : c ∈ L.I) (α β : ℂ) :
    ∃ F : ℂ → ℝ → ℂ,
      (∀ z : ℂ, IsSolution L z g (F z) ∧ F z c = α ∧ quasiDeriv L (F z) c = β) ∧
      (∀ (z : ℂ) (f : ℝ → ℂ), IsSolution L z g f → f c = α → quasiDeriv L f c = β →
        ∀ x ∈ L.I, f x = F z x) ∧
      (∀ x ∈ L.I, Differentiable ℂ (fun z => F z x)) :=
  ⟨IvpAux.solF L g c α β,
    fun z => ⟨IvpAux.sol_isSolution L g c α β hg hc z, IvpAux.solF_c L g c α β hg hc z,
      IvpAux.qd_solF_c L g c α β hg hc z⟩,
    fun z f hf h1 h2 => IvpAux.sol_unique L g c α β hg hc z f hf h1 h2,
    fun _ hx => IvpAux.solF_differentiable L g c α β hg hc hx⟩

namespace VoCAux

theorem voc (L : SLData) (z : ℂ) (g : ℝ → ℂ)
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

end VoCAux


open MeasureTheory Set Filter Topology
open scoped Interval

namespace WeylAux

open TeschlQM.SturmLiouville VoCAux LagAux IvpAux

theorem r_nonneg_of_mem (L : SLData) {s : ℝ} (hs : s ∈ L.I) : 0 ≤ L.r s :=
  (L.r_pos s hs.1 hs.2).le

theorem uIoc_sub_I (L : SLData) {c t : ℝ} (hc : c ∈ L.I) (ht : t ∈ L.I) : Ι c t ⊆ L.I :=
  uIoc_subset_uIcc.trans (uIcc_subset_I L hc ht)

theorem int_r_mul (L : SLData) {φ : ℝ → ℝ} (hφ : ContinuousOn φ L.I) {c t : ℝ} (hc : c ∈ L.I)
    (ht : t ∈ L.I) : IntegrableOn (fun s => L.r s * φ s) (Ι c t) :=
  (iiR L L.r_loc hc ht).def'.mul_continuousOn_of_subset (hφ.mono (uIcc_subset_I L hc ht))
    measurableSet_uIoc isCompact_uIcc uIoc_subset_uIcc

theorem int_r_mul_nonneg (L : SLData) {φ : ℝ → ℝ} (hφ : ∀ s, 0 ≤ φ s) {c t : ℝ}
    (hc : c ∈ L.I) (ht : t ∈ L.I) : 0 ≤ ∫ s in Ι c t, L.r s * φ s :=
  setIntegral_nonneg measurableSet_uIoc
    (fun s hs => mul_nonneg (r_nonneg_of_mem L (uIoc_sub_I L hc ht hs)) (hφ s))

/-- Monotonicity of `t ↦ ∫_{Ι c t} r φ` along `uIcc c x`, for `φ ≥ 0`. -/
theorem int_r_mono (L : SLData) {φ : ℝ → ℝ} (hφc : ContinuousOn φ L.I) (hφ : ∀ s, 0 ≤ φ s)
    {c x t : ℝ} (hc : c ∈ L.I) (hx : x ∈ L.I) (ht : t ∈ uIcc c x) :
    ∫ s in Ι c t, L.r s * φ s ≤ ∫ s in Ι c x, L.r s * φ s :=
  setIntegral_mono_set (int_r_mul L hφc hc hx)
    (ae_restrict_of_forall_mem measurableSet_uIoc
      (fun s hs => mul_nonneg (r_nonneg_of_mem L (uIoc_sub_I L hc hx hs)) (hφ s)))
    (Eventually.of_forall (uIoc_mono_of_mem ht))

/-- Weighted Cauchy–Schwarz inequality on `Ι c t`. -/
theorem cs_weighted (L : SLData) {a b : ℝ → ℝ} (ha : ContinuousOn a L.I)
    (hb : ContinuousOn b L.I) {c t : ℝ} (hc : c ∈ L.I) (ht : t ∈ L.I) :
    (∫ s in Ι c t, L.r s * (a s * b s)) ^ 2 ≤
      (∫ s in Ι c t, L.r s * a s ^ 2) * (∫ s in Ι c t, L.r s * b s ^ 2) := by
  have iA := int_r_mul L (φ := fun s => a s ^ 2) (ha.pow 2) hc ht
  have iB := int_r_mul L (φ := fun s => b s ^ 2) (hb.pow 2) hc ht
  have iAB := int_r_mul L (φ := fun s => a s * b s) (ha.mul hb) hc ht
  have key : ∀ x : ℝ, 0 ≤ (∫ s in Ι c t, L.r s * a s ^ 2) * (x * x) +
      (2 * ∫ s in Ι c t, L.r s * (a s * b s)) * x + (∫ s in Ι c t, L.r s * b s ^ 2) := by
    intro x
    have hnn := int_r_mul_nonneg L (φ := fun s => (x * a s + b s) ^ 2) (fun s => sq_nonneg _)
      hc ht
    have e : (∫ s in Ι c t, L.r s * (x * a s + b s) ^ 2) =
        ∫ s in Ι c t, ((x * x) * (L.r s * a s ^ 2) + (2 * x) * (L.r s * (a s * b s)) +
          L.r s * b s ^ 2) := by
      congr 1; funext s; ring
    have i1 : IntegrableOn (fun s => (x * x) * (L.r s * a s ^ 2)) (Ι c t) := iA.const_mul _
    have i2 : IntegrableOn (fun s => (2 * x) * (L.r s * (a s * b s))) (Ι c t) :=
      iAB.const_mul _
    have i12 : IntegrableOn (fun s => (x * x) * (L.r s * a s ^ 2) +
        (2 * x) * (L.r s * (a s * b s))) (Ι c t) := i1.add i2
    rw [e, integral_add i12 iB, integral_add i1 i2, integral_const_mul,
      integral_const_mul] at hnn
    linarith
  have := discrim_le_zero key
  unfold discrim at this
  linarith

/-- Bound on the variation-of-constants integrals. -/
theorem voc_int_bound (L : SLData) {A u : ℝ → ℂ} (hA : ContinuousOn A L.I)
    (hu : ContinuousOn u L.I) (w : ℂ) {c t : ℝ} (hc : c ∈ L.I) (ht : t ∈ L.I) :
    ‖∫ y in c..t, A y * (w * u y) * (L.r y : ℂ)‖ ^ 2 ≤
      ‖w‖ ^ 2 * ((∫ s in Ι c t, L.r s * ‖A s‖ ^ 2) * (∫ s in Ι c t, L.r s * ‖u s‖ ^ 2)) := by
  have h1 : ‖∫ y in c..t, A y * (w * u y) * (L.r y : ℂ)‖ ≤
      ‖w‖ * ∫ s in Ι c t, L.r s * (‖A s‖ * ‖u s‖) := by
    refine intervalIntegral.norm_integral_le_integral_norm_uIoc.trans (le_of_eq ?_)
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_uIoc (fun s hs => ?_)
    have hr := r_nonneg_of_mem L (uIoc_sub_I L hc ht hs)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    ring
  have h2 := cs_weighted L hA.norm hu.norm hc ht
  have h0 : 0 ≤ ‖∫ y in c..t, A y * (w * u y) * (L.r y : ℂ)‖ := norm_nonneg _
  calc _ ≤ (‖w‖ * ∫ s in Ι c t, L.r s * (‖A s‖ * ‖u s‖)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = ‖w‖ ^ 2 * (∫ s in Ι c t, L.r s * (‖A s‖ * ‖u s‖)) ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- The a-priori estimate behind the independence of square integrability from `z`. -/
theorem core_bound (L : SLData) {u u1 u2 : ℝ → ℂ} (hu : ContinuousOn u L.I)
    (hu1 : ContinuousOn u1 L.I) (hu2 : ContinuousOn u2 L.I) {c : ℝ} (hc : c ∈ L.I)
    (w α β : ℂ)
    (hvoc : ∀ x ∈ L.I, u x = u1 x * (α + ∫ y in c..x, u2 y * (w * u y) * (L.r y : ℂ)) +
      u2 x * (β - ∫ y in c..x, u1 y * (w * u y) * (L.r y : ℂ)))
    {M2 : ℝ} (hM0 : 0 ≤ M2) (hsmall : 4 * ‖w‖ ^ 2 * M2 ^ 2 ≤ 1 / 2)
    {x' : ℝ} (hx' : x' ∈ L.I) (hM : ∫ s in Ι c x', L.r s * (‖u1 s‖ ^ 2 + ‖u2 s‖ ^ 2) ≤ M2) :
    ‖u x'‖ ^ 2 ≤ (2 * (‖α‖ ^ 2 + ‖β‖ ^ 2) + 16 * ‖w‖ ^ 2 * M2 ^ 2 * (‖α‖ ^ 2 + ‖β‖ ^ 2)) *
      (‖u1 x'‖ ^ 2 + ‖u2 x'‖ ^ 2) := by
  set K0 := ‖α‖ ^ 2 + ‖β‖ ^ 2 with hK0
  have hK0n : 0 ≤ K0 := by positivity
  set N := fun t => ∫ s in Ι c t, L.r s * ‖u s‖ ^ 2 with hN
  have hNx : 0 ≤ N x' := int_r_mul_nonneg L (fun s => sq_nonneg _) hc hx'
  have hSc : ContinuousOn (fun s => ‖u1 s‖ ^ 2 + ‖u2 s‖ ^ 2) L.I :=
    (hu1.norm.pow 2).add (hu2.norm.pow 2)
  have hA1 : ∀ t ∈ uIcc c x', ∫ s in Ι c t, L.r s * ‖u1 s‖ ^ 2 ≤ M2 := by
    intro t ht
    refine le_trans ?_ ((int_r_mono L hSc (fun s => by positivity) hc hx' ht).trans hM)
    exact setIntegral_mono_on (int_r_mul L (hu1.norm.pow 2) hc (uIcc_subset_I L hc hx' ht))
      (int_r_mul L hSc hc (uIcc_subset_I L hc hx' ht)) measurableSet_uIoc (fun s hs =>
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg ‖u2 s‖])
          (r_nonneg_of_mem L (uIoc_sub_I L hc (uIcc_subset_I L hc hx' ht) hs)))
  have hA2 : ∀ t ∈ uIcc c x', ∫ s in Ι c t, L.r s * ‖u2 s‖ ^ 2 ≤ M2 := by
    intro t ht
    refine le_trans ?_ ((int_r_mono L hSc (fun s => by positivity) hc hx' ht).trans hM)
    exact setIntegral_mono_on (int_r_mul L (hu2.norm.pow 2) hc (uIcc_subset_I L hc hx' ht))
      (int_r_mul L hSc hc (uIcc_subset_I L hc hx' ht)) measurableSet_uIoc (fun s hs =>
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg ‖u1 s‖])
          (r_nonneg_of_mem L (uIoc_sub_I L hc (uIcc_subset_I L hc hx' ht) hs)))
  have hpt : ∀ t ∈ uIcc c x', ‖u t‖ ^ 2 ≤
      (‖u1 t‖ ^ 2 + ‖u2 t‖ ^ 2) * (2 * K0 + 4 * ‖w‖ ^ 2 * M2 * N x') := by
    intro t ht
    have htI := uIcc_subset_I L hc hx' ht
    have hNt : N t ≤ N x' := int_r_mono L (hu.norm.pow 2) (fun s => sq_nonneg _) hc hx' ht
    have hNt0 : 0 ≤ N t := int_r_mul_nonneg L (fun s => sq_nonneg _) hc htI
    set I2 := ∫ y in c..t, u2 y * (w * u y) * (L.r y : ℂ)
    set I1 := ∫ y in c..t, u1 y * (w * u y) * (L.r y : ℂ)
    have hw2 : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
    have b2 : ‖I2‖ ^ 2 ≤ ‖w‖ ^ 2 * M2 * N x' := by
      refine (voc_int_bound L hu2 hu w hc htI).trans ?_
      have a0 := int_r_mul_nonneg L (fun s => sq_nonneg ‖u2 s‖) hc htI
      have := mul_le_mul (hA2 t ht) hNt hNt0 hM0
      calc _ ≤ ‖w‖ ^ 2 * (M2 * N x') := mul_le_mul_of_nonneg_left this hw2
        _ = _ := by ring
    have b1 : ‖I1‖ ^ 2 ≤ ‖w‖ ^ 2 * M2 * N x' := by
      refine (voc_int_bound L hu1 hu w hc htI).trans ?_
      have := mul_le_mul (hA1 t ht) hNt hNt0 hM0
      calc _ ≤ ‖w‖ ^ 2 * (M2 * N x') := mul_le_mul_of_nonneg_left this hw2
        _ = _ := by ring
    rw [hvoc t htI]
    have tri : ‖u1 t * (α + I2) + u2 t * (β - I1)‖ ≤
        ‖u1 t‖ * ‖α + I2‖ + ‖u2 t‖ * ‖β - I1‖ :=
      (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
    have hA : ‖α + I2‖ ^ 2 ≤ 2 * ‖α‖ ^ 2 + 2 * ‖I2‖ ^ 2 := by
      have := norm_add_le α I2
      nlinarith [norm_nonneg (α + I2), norm_nonneg α, norm_nonneg I2, sq_nonneg (‖α‖ - ‖I2‖)]
    have hB : ‖β - I1‖ ^ 2 ≤ 2 * ‖β‖ ^ 2 + 2 * ‖I1‖ ^ 2 := by
      have := norm_sub_le β I1
      nlinarith [norm_nonneg (β - I1), norm_nonneg β, norm_nonneg I1, sq_nonneg (‖β‖ - ‖I1‖)]
    have h0 : 0 ≤ ‖u1 t * (α + I2) + u2 t * (β - I1)‖ := norm_nonneg _
    have hcs : (‖u1 t‖ * ‖α + I2‖ + ‖u2 t‖ * ‖β - I1‖) ^ 2 ≤
        (‖u1 t‖ ^ 2 + ‖u2 t‖ ^ 2) * (‖α + I2‖ ^ 2 + ‖β - I1‖ ^ 2) := by
      nlinarith [sq_nonneg (‖u1 t‖ * ‖β - I1‖ - ‖u2 t‖ * ‖α + I2‖)]
    calc _ ≤ (‖u1 t‖ * ‖α + I2‖ + ‖u2 t‖ * ‖β - I1‖) ^ 2 := pow_le_pow_left₀ h0 tri 2
      _ ≤ (‖u1 t‖ ^ 2 + ‖u2 t‖ ^ 2) * (‖α + I2‖ ^ 2 + ‖β - I1‖ ^ 2) := hcs
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [hK0]; nlinarith
  set B := 2 * K0 + 4 * ‖w‖ ^ 2 * M2 * N x' with hB
  have hB0 : 0 ≤ B := by positivity
  have hNle : N x' ≤ (∫ s in Ι c x', L.r s * (‖u1 s‖ ^ 2 + ‖u2 s‖ ^ 2)) * B := by
    rw [← integral_mul_const]
    refine setIntegral_mono_on (int_r_mul L (hu.norm.pow 2) hc hx')
      ((int_r_mul L hSc hc hx').mul_const B) measurableSet_uIoc (fun s hs => ?_)
    have hr := r_nonneg_of_mem L (uIoc_sub_I L hc hx' hs)
    have := mul_le_mul_of_nonneg_left (hpt s (uIoc_subset_uIcc hs)) hr
    calc _ ≤ _ := this
      _ = _ := by ring
  have hNb : N x' ≤ 4 * K0 * M2 := by
    have h1 : N x' ≤ M2 * B := hNle.trans (mul_le_mul_of_nonneg_right hM hB0)
    rw [hB] at h1
    nlinarith [mul_le_mul_of_nonneg_right hsmall hNx]
  refine (hpt x' right_mem_uIcc).trans ?_
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hNb (by positivity : (0:ℝ) ≤ 4 * ‖w‖ ^ 2 * M2)]

end WeylAux


open MeasureTheory Set Filter Topology
open scoped Interval

namespace WeylAux

open TeschlQM.SturmLiouville VoCAux LagAux IvpAux

theorem sol_contOn (L : SLData) {z : ℂ} {g u : ℝ → ℂ} (hu : IsSolution L z g u) :
    ContinuousOn u L.I := by
  obtain ⟨c, hc⟩ := exists_mem_I L
  obtain ⟨⟨-, hl, hp⟩, -, -⟩ := hu
  refine ((continuousOn_const (c := u c)).add (contOn_prim L hl hc)).congr (fun x hx => ?_)
  have := hp c hc x hx
  beta_reduce at this ⊢
  simp only [Pi.add_apply]
  rw [← this]; ring

theorem qd_contOn (L : SLData) {z : ℂ} {g u : ℝ → ℂ} (hu : IsSolution L z g u) :
    ContinuousOn (quasiDeriv L u) L.I := by
  obtain ⟨c, hc⟩ := exists_mem_I L
  obtain ⟨-, hl, hp⟩ := hu
  refine ((continuousOn_const (c := quasiDeriv L u c)).add (contOn_prim L hl hc)).congr (fun x hx => ?_)
  have := hp c hc x hx
  beta_reduce at this ⊢
  simp only [Pi.add_apply]
  rw [← this]; ring

theorem zero_loc (L : SLData) :
    LocallyIntegrableOn (fun x => (L.r x : ℂ) * (0 : ℝ → ℂ) x) L.I := by
  have : (fun x => (L.r x : ℂ) * (0 : ℝ → ℂ) x) = fun _ => (0 : ℂ) := by funext x; simp
  rw [this]; exact locallyIntegrableOn_const 0

/-- A fundamental system with Wronskian one. -/
theorem fund_system (L : SLData) (z : ℂ) :
    ∃ u₁ u₂ : ℝ → ℂ, IsSolution L z 0 u₁ ∧ IsSolution L z 0 u₂ ∧
      ∀ x ∈ L.I, wronskian L x u₁ u₂ = 1 := by
  obtain ⟨c, hc⟩ := exists_mem_I L
  obtain ⟨F1, hF1, -, -⟩ := IvpAux.ivp L 0 (zero_loc L) c hc 1 0
  obtain ⟨F2, hF2, -, -⟩ := IvpAux.ivp L 0 (zero_loc L) c hc 0 1
  obtain ⟨h1, h1a, h1b⟩ := hF1 z
  obtain ⟨h2, h2a, h2b⟩ := hF2 z
  refine ⟨F1 z, F2 z, h1, h2, fun x hx => ?_⟩
  have hd := wronskian_diff L h2 h1 hc hx
  have e : ∫ t in c..x, (L.r t : ℂ) * ((z * F1 z t + (0 : ℝ → ℂ) t) * F2 z t -
      F1 z t * (z * F2 z t + (0 : ℝ → ℂ) t)) = 0 := by
    rw [← intervalIntegral.integral_zero]
    congr 1; funext t; simp only [Pi.zero_apply, add_zero]; ring
  rw [e, sub_eq_zero] at hd
  rw [hd]
  unfold wronskian
  rw [h1a, h1b, h2a, h2b]; ring

theorem isOpen_gt_a (L : SLData) : IsOpen {x : ℝ | L.a < (x : EReal)} :=
  isOpen_lt continuous_const continuous_coe_real_ereal

theorem isOpen_lt_b (L : SLData) : IsOpen {x : ℝ | (x : EReal) < L.b} :=
  isOpen_lt continuous_coe_real_ereal continuous_const

theorem measSL (L : SLData) (c : ℝ) : MeasurableSet {x : ℝ | L.a < (x : EReal) ∧ x < c} :=
  ((isOpen_gt_a L).inter isOpen_Iio).measurableSet

theorem measSR (L : SLData) (c : ℝ) : MeasurableSet {x : ℝ | c < x ∧ (x : EReal) < L.b} :=
  (isOpen_Ioi.inter (isOpen_lt_b L)).measurableSet

theorem SL_sub (L : SLData) {c : ℝ} (hc : c ∈ L.I) :
    {x : ℝ | L.a < (x : EReal) ∧ x < c} ⊆ L.I :=
  fun x hx => ⟨hx.1, lt_trans (EReal.coe_lt_coe_iff.mpr hx.2) hc.2⟩

theorem SR_sub (L : SLData) {c : ℝ} (hc : c ∈ L.I) :
    {x : ℝ | c < x ∧ (x : EReal) < L.b} ⊆ L.I :=
  fun x hx => ⟨lt_trans hc.1 (EReal.coe_lt_coe_iff.mpr hx.1), hx.2⟩

/-- From weighted `L²` to integrability of `r |u|²`. -/
theorem memLp_integrable (L : SLData) {S : Set ℝ} (hS : MeasurableSet S) (hSI : S ⊆ L.I)
    {u : ℝ → ℂ}
    (hu : MemLp u 2 ((volume.restrict S).withDensity (fun x => ENNReal.ofReal (L.r x)))) :
    IntegrableOn (fun s => L.r s * ‖u s‖ ^ 2) S := by
  have h1 := (memLp_two_iff_integrable_sq_norm hu.1).mp hu
  have hr : AEMeasurable (fun x => (L.r x).toNNReal) (volume.restrict S) :=
    (L.r_loc.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono hSI le_rfl)).aemeasurable.real_toNNReal
  have h2 := (integrable_withDensity_iff_integrable_smul₀ hr).mp h1
  refine h2.congr (ae_restrict_of_forall_mem hS (fun x hx => ?_))
  have hx0 := (L.r_pos x (hSI hx).1 (hSI hx).2).le
  simp only [NNReal.smul_def, Real.coe_toNNReal _ hx0, smul_eq_mul]

theorem memLp_mono_set (L : SLData) {S T : Set ℝ} (hS : MeasurableSet S) (hST : S ⊆ T)
    {u : ℝ → ℂ}
    (hu : MemLp u 2 ((volume.restrict T).withDensity (fun x => ENNReal.ofReal (L.r x)))) :
    MemLp u 2 ((volume.restrict S).withDensity (fun x => ENNReal.ofReal (L.r x))) := by
  refine hu.mono_measure ?_
  rw [← Measure.restrict_restrict_of_subset hST, ← restrict_withDensity hS]
  exact Measure.restrict_le_self

/-- Domination by two weighted `L²` functions. -/
theorem memLp_of_bound (L : SLData) {S : Set ℝ} (hS : MeasurableSet S) (hSI : S ⊆ L.I)
    {u u1 u2 : ℝ → ℂ} (hu : ContinuousOn u L.I)
    (h1 : MemLp u1 2 ((volume.restrict S).withDensity (fun x => ENNReal.ofReal (L.r x))))
    (h2 : MemLp u2 2 ((volume.restrict S).withDensity (fun x => ENNReal.ofReal (L.r x))))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x ∈ S, ‖u x‖ ^ 2 ≤ C * (‖u1 x‖ ^ 2 + ‖u2 x‖ ^ 2)) :
    MemLp u 2 ((volume.restrict S).withDensity (fun x => ENNReal.ofReal (L.r x))) := by
  have hg := (h1.norm.add h2.norm).const_mul (Real.sqrt C)
  refine hg.of_le ((hu.mono hSI).aestronglyMeasurable hS |>.mono_ac
    (withDensity_absolutelyContinuous _ _)) ?_
  refine (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_of_forall_mem hS (fun x hx => ?_))
  have hx := hb x hx
  have e1 : ‖u x‖ = Real.sqrt (‖u x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
  have hn : 0 ≤ ‖u1 x‖ + ‖u2 x‖ := by positivity
  simp only [Pi.add_apply, Real.norm_eq_abs, norm_mul]
  rw [abs_of_nonneg hn, e1, ← Real.sqrt_sq hn, abs_of_nonneg (Real.sqrt_nonneg C),
    ← Real.sqrt_mul hC]
  refine Real.sqrt_le_sqrt (hx.trans (mul_le_mul_of_nonneg_left ?_ hC))
  nlinarith [norm_nonneg (u1 x), norm_nonneg (u2 x)]

end WeylAux


open MeasureTheory Set Filter Topology
open scoped Interval

namespace WeylAux

open TeschlQM.SturmLiouville VoCAux LagAux IvpAux

theorem tail_small_left (L : SLData) {Φ : ℝ → ℝ} {c3 : ℝ} (hc3 : c3 ∈ L.I)
    (hΦ : IntegrableOn Φ {x : ℝ | L.a < (x : EReal) ∧ x < c3}) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c ∈ L.I, c < c3 ∧ ∫ x in {x : ℝ | L.a < (x : EReal) ∧ x < c3} ∩ Iic c, Φ x < δ := by
  have hT : Tendsto (fun c => ∫ x in {x : ℝ | L.a < (x : EReal) ∧ x < c3},
      (Iic c).indicator Φ x) L.atLeft (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (l := L.atLeft)
      (μ := volume.restrict {x : ℝ | L.a < (x : EReal) ∧ x < c3})
      (F := fun c => (Iic c).indicator Φ) (f := fun _ => (0 : ℝ)) (fun x => ‖Φ x‖)
      (Eventually.of_forall (fun c => hΦ.aestronglyMeasurable.indicator measurableSet_Iic))
      (Eventually.of_forall (fun c => Eventually.of_forall (fun x =>
        norm_indicator_le_norm_self _ _))) hΦ.norm
      (ae_restrict_of_forall_mem (measSL L c3) (fun x hx => tendsto_const_nhds.congr'
        ((eventually_lt_left L hx.1).mono (fun c hc =>
          (indicator_of_notMem (show x ∉ Iic c from not_le.mpr hc) Φ).symm))))
    simpa using this
  have hev := (hT.eventually (gt_mem_nhds hδ)).and
    ((eventually_mem_left L).and (eventually_lt_left L hc3.1))
  obtain ⟨c, h1, h2, h3⟩ := hev.exists
  refine ⟨c, h2, h3, ?_⟩
  rw [← setIntegral_indicator measurableSet_Iic]
  exact h1

theorem tail_small_right (L : SLData) {Φ : ℝ → ℝ} {c3 : ℝ} (hc3 : c3 ∈ L.I)
    (hΦ : IntegrableOn Φ {x : ℝ | c3 < x ∧ (x : EReal) < L.b}) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c ∈ L.I, c3 < c ∧ ∫ x in {x : ℝ | c3 < x ∧ (x : EReal) < L.b} ∩ Ici c, Φ x < δ := by
  have hT : Tendsto (fun c => ∫ x in {x : ℝ | c3 < x ∧ (x : EReal) < L.b},
      (Ici c).indicator Φ x) L.atRight (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (l := L.atRight)
      (μ := volume.restrict {x : ℝ | c3 < x ∧ (x : EReal) < L.b})
      (F := fun c => (Ici c).indicator Φ) (f := fun _ => (0 : ℝ)) (fun x => ‖Φ x‖)
      (Eventually.of_forall (fun c => hΦ.aestronglyMeasurable.indicator measurableSet_Ici))
      (Eventually.of_forall (fun c => Eventually.of_forall (fun x =>
        norm_indicator_le_norm_self _ _))) hΦ.norm
      (ae_restrict_of_forall_mem (measSR L c3) (fun x hx => tendsto_const_nhds.congr'
        ((eventually_gt_right L hx.2).mono (fun c hc =>
          (indicator_of_notMem (show x ∉ Ici c from not_le.mpr hc) Φ).symm))))
    simpa using this
  have hev := (hT.eventually (gt_mem_nhds hδ)).and
    ((eventually_mem_right L).and (eventually_gt_right L hc3.2))
  obtain ⟨c, h1, h2, h3⟩ := hev.exists
  refine ⟨c, h2, h3, ?_⟩
  rw [← setIntegral_indicator measurableSet_Ici]
  exact h1

theorem small_delta (w : ℂ) :
    0 < 1 / (4 * (‖w‖ + 1)) ∧ 4 * ‖w‖ ^ 2 * (1 / (4 * (‖w‖ + 1))) ^ 2 ≤ 1 / 2 := by
  have hw := norm_nonneg w
  refine ⟨by positivity, ?_⟩
  have h1 : ‖w‖ * (1 / (4 * (‖w‖ + 1))) ≤ 1 / 4 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]; nlinarith
  have h2 : 0 ≤ ‖w‖ * (1 / (4 * (‖w‖ + 1))) := by positivity
  nlinarith

theorem shift_solution (L : SLData) {z z0 : ℂ} {u : ℝ → ℂ} (hu : IsSolution L z 0 u) :
    IsSolution L z0 (fun x => (z - z0) * u x) u := by
  have e : (fun x => z0 * u x + (fun x => (z - z0) * u x) x) =
      (fun x => z * u x + (0 : ℝ → ℂ) x) := by
    funext x; simp only [Pi.zero_apply]; ring
  show SolvesTau L u _
  rw [e]; exact hu

theorem sqInt_all_z_left (L : SLData) (z0 : ℂ)
    (H : ∀ u : ℝ → ℂ, IsSolution L z0 0 u → IsSqIntegrableNearLeft L u)
    (z : ℂ) (u : ℝ → ℂ) (hu : IsSolution L z 0 u) : IsSqIntegrableNearLeft L u := by
  obtain ⟨u1, u2, h1, h2, hW⟩ := fund_system L z0
  obtain ⟨c1, hc1, m1⟩ := H u1 h1
  obtain ⟨c2, hc2, m2⟩ := H u2 h2
  set c3 := min c1 c2 with hc3def
  have hc3 : c3 ∈ L.I := by rcases min_choice c1 c2 with h | h <;> rw [hc3def, h] <;> assumption
  have s1 : {x : ℝ | L.a < (x : EReal) ∧ x < c3} ⊆ {x : ℝ | L.a < (x : EReal) ∧ x < c1} :=
    fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_left _ _)⟩
  have s2 : {x : ℝ | L.a < (x : EReal) ∧ x < c3} ⊆ {x : ℝ | L.a < (x : EReal) ∧ x < c2} :=
    fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_right _ _)⟩
  have m1' := memLp_mono_set L (measSL L c3) s1 m1
  have m2' := memLp_mono_set L (measSL L c3) s2 m2
  have i1 := memLp_integrable L (measSL L c3) (SL_sub L hc3) m1'
  have i2 := memLp_integrable L (measSL L c3) (SL_sub L hc3) m2'
  have hΦ : IntegrableOn (fun s => L.r s * (‖u1 s‖ ^ 2 + ‖u2 s‖ ^ 2))
      {x : ℝ | L.a < (x : EReal) ∧ x < c3} :=
    IntegrableOn.congr_fun (i1.add i2) (fun s _ => by simp only [Pi.add_apply]; ring) (measSL L c3)
  set w := z - z0 with hw
  obtain ⟨hδ, hsmall⟩ := small_delta w
  obtain ⟨c, hc, hcc3, hint⟩ := tail_small_left L hc3 hΦ hδ
  set M2 := ∫ x in {x : ℝ | L.a < (x : EReal) ∧ x < c3} ∩ Iic c,
    L.r x * (‖u1 x‖ ^ 2 + ‖u2 x‖ ^ 2) with hM2
  have hM0 : 0 ≤ M2 := setIntegral_nonneg ((measSL L c3).inter measurableSet_Iic)
    (fun s hs => mul_nonneg (r_nonneg_of_mem L (SL_sub L hc3 hs.1)) (by positivity))
  have hsm : 4 * ‖w‖ ^ 2 * M2 ^ 2 ≤ 1 / 2 := by
    refine le_trans ?_ hsmall
    have : M2 ^ 2 ≤ (1 / (4 * (‖w‖ + 1))) ^ 2 := pow_le_pow_left₀ hM0 hint.le 2
    have h4 : 0 ≤ 4 * ‖w‖ ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left this h4
  obtain ⟨α, β, hv⟩ := voc L z0 (fun x => w * u x) u1 u2 h1 h2 hW c hc u (shift_solution L hu)
  have hsubc : {x : ℝ | L.a < (x : EReal) ∧ x < c} ⊆ {x : ℝ | L.a < (x : EReal) ∧ x < c3} :=
    fun x hx => ⟨hx.1, hx.2.trans hcc3⟩
  refine ⟨c, hc, memLp_of_bound L (measSL L c) (SL_sub L hc) (sol_contOn L hu)
    (memLp_mono_set L (measSL L c) hsubc m1') (memLp_mono_set L (measSL L c) hsubc m2')
    (C := 2 * (‖α‖ ^ 2 + ‖β‖ ^ 2) + 16 * ‖w‖ ^ 2 * M2 ^ 2 * (‖α‖ ^ 2 + ‖β‖ ^ 2))
    (by positivity) (fun x hx => ?_)⟩
  have hxI := SL_sub L hc hx
  refine core_bound L (sol_contOn L hu) (sol_contOn L h1) (sol_contOn L h2) hc w α β
    (fun x hx => (hv x hx).1) hM0 hsm hxI ?_
  rw [uIoc_of_ge hx.2.le]
  refine setIntegral_mono_set (hΦ.mono_set inter_subset_left)
    (ae_restrict_of_forall_mem ((measSL L c3).inter measurableSet_Iic)
      (fun s hs => mul_nonneg (r_nonneg_of_mem L (SL_sub L hc3 hs.1)) (by positivity)))
    (Eventually.of_forall (fun s hs => ?_))
  exact ⟨⟨lt_trans hx.1 (EReal.coe_lt_coe_iff.mpr hs.1), lt_of_le_of_lt hs.2 hcc3⟩, hs.2⟩

theorem sqInt_all_z_right (L : SLData) (z0 : ℂ)
    (H : ∀ u : ℝ → ℂ, IsSolution L z0 0 u → IsSqIntegrableNearRight L u)
    (z : ℂ) (u : ℝ → ℂ) (hu : IsSolution L z 0 u) : IsSqIntegrableNearRight L u := by
  obtain ⟨u1, u2, h1, h2, hW⟩ := fund_system L z0
  obtain ⟨c1, hc1, m1⟩ := H u1 h1
  obtain ⟨c2, hc2, m2⟩ := H u2 h2
  set c3 := max c1 c2 with hc3def
  have hc3 : c3 ∈ L.I := by rcases max_choice c1 c2 with h | h <;> rw [hc3def, h] <;> assumption
  have s1 : {x : ℝ | c3 < x ∧ (x : EReal) < L.b} ⊆ {x : ℝ | c1 < x ∧ (x : EReal) < L.b} :=
    fun x hx => ⟨lt_of_le_of_lt (le_max_left _ _) hx.1, hx.2⟩
  have s2 : {x : ℝ | c3 < x ∧ (x : EReal) < L.b} ⊆ {x : ℝ | c2 < x ∧ (x : EReal) < L.b} :=
    fun x hx => ⟨lt_of_le_of_lt (le_max_right _ _) hx.1, hx.2⟩
  have m1' := memLp_mono_set L (measSR L c3) s1 m1
  have m2' := memLp_mono_set L (measSR L c3) s2 m2
  have i1 := memLp_integrable L (measSR L c3) (SR_sub L hc3) m1'
  have i2 := memLp_integrable L (measSR L c3) (SR_sub L hc3) m2'
  have hΦ : IntegrableOn (fun s => L.r s * (‖u1 s‖ ^ 2 + ‖u2 s‖ ^ 2))
      {x : ℝ | c3 < x ∧ (x : EReal) < L.b} :=
    IntegrableOn.congr_fun (i1.add i2) (fun s _ => by simp only [Pi.add_apply]; ring) (measSR L c3)
  set w := z - z0 with hw
  obtain ⟨hδ, hsmall⟩ := small_delta w
  obtain ⟨c, hc, hcc3, hint⟩ := tail_small_right L hc3 hΦ hδ
  set M2 := ∫ x in {x : ℝ | c3 < x ∧ (x : EReal) < L.b} ∩ Ici c,
    L.r x * (‖u1 x‖ ^ 2 + ‖u2 x‖ ^ 2) with hM2
  have hM0 : 0 ≤ M2 := setIntegral_nonneg ((measSR L c3).inter measurableSet_Ici)
    (fun s hs => mul_nonneg (r_nonneg_of_mem L (SR_sub L hc3 hs.1)) (by positivity))
  have hsm : 4 * ‖w‖ ^ 2 * M2 ^ 2 ≤ 1 / 2 := by
    refine le_trans ?_ hsmall
    have : M2 ^ 2 ≤ (1 / (4 * (‖w‖ + 1))) ^ 2 := pow_le_pow_left₀ hM0 hint.le 2
    have h4 : 0 ≤ 4 * ‖w‖ ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left this h4
  obtain ⟨α, β, hv⟩ := voc L z0 (fun x => w * u x) u1 u2 h1 h2 hW c hc u (shift_solution L hu)
  have hsubc : {x : ℝ | c < x ∧ (x : EReal) < L.b} ⊆ {x : ℝ | c3 < x ∧ (x : EReal) < L.b} :=
    fun x hx => ⟨hcc3.trans hx.1, hx.2⟩
  refine ⟨c, hc, memLp_of_bound L (measSR L c) (SR_sub L hc) (sol_contOn L hu)
    (memLp_mono_set L (measSR L c) hsubc m1') (memLp_mono_set L (measSR L c) hsubc m2')
    (C := 2 * (‖α‖ ^ 2 + ‖β‖ ^ 2) + 16 * ‖w‖ ^ 2 * M2 ^ 2 * (‖α‖ ^ 2 + ‖β‖ ^ 2))
    (by positivity) (fun x hx => ?_)⟩
  have hxI := SR_sub L hc hx
  refine core_bound L (sol_contOn L hu) (sol_contOn L h1) (sol_contOn L h2) hc w α β
    (fun x hx => (hv x hx).1) hM0 hsm hxI ?_
  rw [uIoc_of_le hx.1.le]
  refine setIntegral_mono_set (hΦ.mono_set inter_subset_left)
    (ae_restrict_of_forall_mem ((measSR L c3).inter measurableSet_Ici)
      (fun s hs => mul_nonneg (r_nonneg_of_mem L (SR_sub L hc3 hs.1)) (by positivity)))
    (Eventually.of_forall (fun s hs => ?_))
  exact ⟨⟨lt_trans hcc3 hs.1, lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr hs.2) hx.2⟩, hs.1.le⟩

theorem sqIntegrable_all_z (L : SLData) :
    ((∃ z₀ : ℂ, ∀ u : ℝ → ℂ, IsSolution L z₀ 0 u → IsSqIntegrableNearLeft L u) →
      ∀ z : ℂ, ∀ u : ℝ → ℂ, IsSolution L z 0 u → IsSqIntegrableNearLeft L u) ∧
    ((∃ z₀ : ℂ, ∀ u : ℝ → ℂ, IsSolution L z₀ 0 u → IsSqIntegrableNearRight L u) →
      ∀ z : ℂ, ∀ u : ℝ → ℂ, IsSolution L z 0 u → IsSqIntegrableNearRight L u) :=
  ⟨fun ⟨z0, H⟩ z u hu => sqInt_all_z_left L z0 H z u hu,
    fun ⟨z0, H⟩ z u hu => sqInt_all_z_right L z0 H z u hu⟩

end WeylAux


open MeasureTheory Set Filter Topology
open scoped Interval

namespace WeylAux

open TeschlQM.SturmLiouville VoCAux LagAux IvpAux

theorem intOn_Ioc (L : SLData) {φ : ℝ → ℂ} (hφ : ContinuousOn φ L.I) {c d : ℝ} (hc : c ∈ L.I)
    (hd : d ∈ L.I) (hcd : c ≤ d) : IntegrableOn (fun x => φ x * (L.r x : ℂ)) (Ioc c d) := by
  have hsub : Icc c d ⊆ L.I := by rw [← uIcc_of_le hcd]; exact uIcc_subset_I L hc hd
  have hr : IntegrableOn (fun x => (L.r x : ℂ)) (Icc c d) :=
    (r_loc' L).integrableOn_compact_subset hsub isCompact_Icc
  exact ((hr.mono_set Ioc_subset_Icc_self).mul_continuousOn_of_subset (hφ.mono hsub)
    measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self).congr_fun
    (fun x _ => mul_comm _ _) measurableSet_Ioc

/-- Two solutions with Wronskian one are linearly independent on every open subinterval. -/
theorem indep_on_interval (L : SLData) {z : ℂ} {u1 u2 : ℝ → ℂ} (h1 : IsSolution L z 0 u1)
    (h2 : IsSolution L z 0 u2) (hW : ∀ x ∈ L.I, wronskian L x u1 u2 = 1) {c d : ℝ}
    (hc : c ∈ L.I) (hd : d ∈ L.I) (hcd : c < d) (a1 a2 : ℂ)
    (h0 : ∀ x ∈ Ioo c d, a1 * u1 x + a2 * u2 x = 0) : a1 = 0 ∧ a2 = 0 := by
  set s := c + (d - c) / 3
  set t := c + 2 * (d - c) / 3
  have hcs : c < s := by simp only [s]; linarith
  have hst : s < t := by simp only [s, t]; linarith
  have htd : t < d := by simp only [t]; linarith
  have hsubI : Icc c d ⊆ L.I := by rw [← uIcc_of_le hcd.le]; exact uIcc_subset_I L hc hd
  have hs : s ∈ L.I := hsubI ⟨hcs.le, (hst.trans htd).le⟩
  have ht : t ∈ L.I := hsubI ⟨(hcs.trans hst).le, htd.le⟩
  have hstI : Icc s t ⊆ L.I := fun x hx => hsubI ⟨hcs.le.trans hx.1, hx.2.trans htd.le⟩
  have hq1 := qd_contOn L h1
  have hq2 := qd_contOn L h2
  obtain ⟨⟨-, hl1, hp1⟩, -, -⟩ := h1
  obtain ⟨⟨-, hl2, hp2⟩, -, -⟩ := h2
  set w1 := fun x => a1 * quasiDeriv L u1 x + a2 * quasiDeriv L u2 x
  have hii : IntervalIntegrable (fun x => w1 x / (L.p x : ℂ)) volume s t := by
    have e : (fun x => w1 x / (L.p x : ℂ)) = fun x => a1 * (quasiDeriv L u1 x / (L.p x : ℂ)) +
        a2 * (quasiDeriv L u2 x / (L.p x : ℂ)) := by funext x; simp only [w1]; ring
    rw [e]
    exact ((ii_of_loc L hl1 hs ht).const_mul a1).add ((ii_of_loc L hl2 hs ht).const_mul a2)
  have hz : ∀ y ∈ Icc s t, ∫ x in s..y, w1 x / (L.p x : ℂ) = 0 := by
    intro y hy
    have hyI := hstI hy
    have e : (fun x => w1 x / (L.p x : ℂ)) = fun x => a1 * (quasiDeriv L u1 x / (L.p x : ℂ)) +
        a2 * (quasiDeriv L u2 x / (L.p x : ℂ)) := by funext x; simp only [w1]; ring
    rw [e, intervalIntegral.integral_add ((ii_of_loc L hl1 hs hyI).const_mul a1)
      ((ii_of_loc L hl2 hs hyI).const_mul a2), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, ← hp1 s hs y hyI, ← hp2 s hs y hyI]
    have e1 := h0 y ⟨hcs.trans_le hy.1, hy.2.trans_lt htd⟩
    have e2 := h0 s ⟨hcs, hst.trans htd⟩
    linear_combination e1 - e2
  have hae := ae_zero_local hii hz
  have hae2 : w1 =ᵐ[volume.restrict (Ioo s t)] (fun _ => (0 : ℂ)) := by
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with x hx hmem
    have hxI : x ∈ L.I := hstI (Ioo_subset_Icc_self hmem)
    have hp : (L.p x : ℂ) ≠ 0 := by exact_mod_cast (L.p_pos x hxI.1 hxI.2).ne'
    rcases div_eq_zero_iff.mp hx with h | h
    · exact h
    · exact absurd h hp
  have hw1c : ContinuousOn w1 (Ioo s t) :=
    ((continuousOn_const.mul hq1).add (continuousOn_const.mul hq2)).mono
      (fun x hx => hstI (Ioo_subset_Icc_self hx))
  set m := (s + t) / 2
  have hm : m ∈ Ioo s t := ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
  have E2 : a1 * quasiDeriv L u1 m + a2 * quasiDeriv L u2 m = 0 :=
    Measure.eqOn_open_of_ae_eq hae2 isOpen_Ioo hw1c continuousOn_const hm
  have E1 : a1 * u1 m + a2 * u2 m = 0 := h0 m ⟨hcs.trans hm.1, hm.2.trans htd⟩
  have hWm := hW m (hstI (Ioo_subset_Icc_self hm))
  unfold wronskian at hWm
  constructor
  · linear_combination quasiDeriv L u2 m * E1 - u2 m * E2 - a1 * hWm
  · linear_combination u1 m * E2 - quasiDeriv L u1 m * E1 - a2 * hWm

/-- If `∫ conj w * w * r = 0` over `(c, d]` then `w = 0` on `(c, d)`. -/
theorem zero_of_gram (L : SLData) {w : ℝ → ℂ} (hw : ContinuousOn w L.I) {c d : ℝ}
    (hc : c ∈ L.I) (hd : d ∈ L.I) (hcd : c < d)
    (h : ∫ x in Ioc c d, starRingEnd ℂ (w x) * w x * (L.r x : ℂ) = 0) :
    ∀ x ∈ Ioo c d, w x = 0 := by
  have hsubI : Icc c d ⊆ L.I := by rw [← uIcc_of_le hcd.le]; exact uIcc_subset_I L hc hd
  have e : (fun x => starRingEnd ℂ (w x) * w x * (L.r x : ℂ)) =
      fun x => ((‖w x‖ ^ 2 * L.r x : ℝ) : ℂ) := by
    funext x; rw [Complex.conj_mul']; push_cast; ring
  rw [e, integral_complex_ofReal, Complex.ofReal_eq_zero] at h
  have hint : IntegrableOn (fun x => ‖w x‖ ^ 2 * L.r x) (Ioc c d) := by
    have := (intOn_Ioc L (φ := fun x => ((‖w x‖ ^ 2 : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp_continuousOn (hw.norm.pow 2)) hc hd hcd.le).norm
    refine IntegrableOn.congr_fun this (fun x hx => ?_) measurableSet_Ioc
    have hr := r_nonneg_of_mem L (hsubI (Ioc_subset_Icc_self hx))
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    rw [abs_of_nonneg (sq_nonneg ‖w x‖)]
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc c d)] fun x => ‖w x‖ ^ 2 * L.r x :=
    ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => mul_nonneg (sq_nonneg _)
      (r_nonneg_of_mem L (hsubI (Ioc_subset_Icc_self hx))))
  have hz := (setIntegral_eq_zero_iff_of_nonneg_ae hnn hint).mp h
  have hz2 : w =ᵐ[volume.restrict (Ioo c d)] (fun _ => (0 : ℂ)) := by
    have hz' := ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self hz
    filter_upwards [hz', ae_restrict_mem measurableSet_Ioo] with x hx hmem
    have hxI := hsubI (Ioo_subset_Icc_self hmem)
    have hr := L.r_pos x hxI.1 hxI.2
    simp only [Pi.zero_apply, mul_eq_zero, hr.ne', or_false] at hx
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx)
  intro x hx
  exact Measure.eqOn_open_of_ae_eq hz2 isOpen_Ioo
    (hw.mono (fun y hy => hsubI (Ioo_subset_Icc_self hy))) continuousOn_const hx

end WeylAux


open MeasureTheory Set Filter Topology
open scoped Interval

namespace WeylAux

open TeschlQM.SturmLiouville VoCAux LagAux IvpAux

/-- Gram matrix entries `∫_{(c,d]} conj f * g * r`. -/
noncomputable def gram (L : SLData) (c d : ℝ) (f g : ℝ → ℂ) : ℂ :=
  ∫ x in Ioc c d, starRingEnd ℂ (f x) * g x * (L.r x : ℂ)

theorem gram_int (L : SLData) {f g : ℝ → ℂ} (hf : ContinuousOn f L.I) (hg : ContinuousOn g L.I)
    {c d : ℝ} (hc : c ∈ L.I) (hd : d ∈ L.I) (hcd : c ≤ d) :
    IntegrableOn (fun x => starRingEnd ℂ (f x) * g x * (L.r x : ℂ)) (Ioc c d) :=
  intOn_Ioc L ((Complex.continuous_conj.comp_continuousOn hf).mul hg) hc hd hcd

theorem gram_quad (L : SLData) {u1 u2 : ℝ → ℂ} (hu1 : ContinuousOn u1 L.I)
    (hu2 : ContinuousOn u2 L.I) {c d : ℝ} (hc : c ∈ L.I) (hd : d ∈ L.I) (hcd : c ≤ d)
    (a1 a2 : ℂ) :
    gram L c d (fun x => a1 * u1 x + a2 * u2 x) (fun x => a1 * u1 x + a2 * u2 x) =
      starRingEnd ℂ a1 * a1 * gram L c d u1 u1 + starRingEnd ℂ a1 * a2 * gram L c d u1 u2 +
      starRingEnd ℂ a2 * a1 * gram L c d u2 u1 + starRingEnd ℂ a2 * a2 * gram L c d u2 u2 := by
  unfold gram
  have i11 := (gram_int L hu1 hu1 hc hd hcd).const_mul (starRingEnd ℂ a1 * a1)
  have i12 := (gram_int L hu1 hu2 hc hd hcd).const_mul (starRingEnd ℂ a1 * a2)
  have i21 := (gram_int L hu2 hu1 hc hd hcd).const_mul (starRingEnd ℂ a2 * a1)
  have i22 := (gram_int L hu2 hu2 hc hd hcd).const_mul (starRingEnd ℂ a2 * a2)
  have e : (fun x => starRingEnd ℂ (a1 * u1 x + a2 * u2 x) * (a1 * u1 x + a2 * u2 x) *
      (L.r x : ℂ)) = fun x =>
      starRingEnd ℂ a1 * a1 * (starRingEnd ℂ (u1 x) * u1 x * (L.r x : ℂ)) +
      starRingEnd ℂ a1 * a2 * (starRingEnd ℂ (u1 x) * u2 x * (L.r x : ℂ)) +
      starRingEnd ℂ a2 * a1 * (starRingEnd ℂ (u2 x) * u1 x * (L.r x : ℂ)) +
      starRingEnd ℂ a2 * a2 * (starRingEnd ℂ (u2 x) * u2 x * (L.r x : ℂ)) := by
    funext x; simp only [map_add, map_mul]; ring
  set A := fun x => starRingEnd ℂ a1 * a1 * (starRingEnd ℂ (u1 x) * u1 x * (L.r x : ℂ))
  set B := fun x => starRingEnd ℂ a1 * a2 * (starRingEnd ℂ (u1 x) * u2 x * (L.r x : ℂ))
  set C := fun x => starRingEnd ℂ a2 * a1 * (starRingEnd ℂ (u2 x) * u1 x * (L.r x : ℂ))
  set E := fun x => starRingEnd ℂ a2 * a2 * (starRingEnd ℂ (u2 x) * u2 x * (L.r x : ℂ))
  have iAB : IntegrableOn (fun x => A x + B x) (Ioc c d) := i11.add i12
  have iABC : IntegrableOn (fun x => A x + B x + C x) (Ioc c d) := iAB.add i21
  have e2 : (fun x => starRingEnd ℂ (a1 * u1 x + a2 * u2 x) * (a1 * u1 x + a2 * u2 x) *
      (L.r x : ℂ)) = fun x => A x + B x + C x + E x := e
  rw [e2, integral_add iABC i22, integral_add iAB i21, integral_add i11 i12]
  simp only [A, B, C, E, integral_const_mul]

theorem gram_ne (L : SLData) {z : ℂ} {u1 u2 : ℝ → ℂ} (h1 : IsSolution L z 0 u1)
    (h2 : IsSolution L z 0 u2) (hW : ∀ x ∈ L.I, wronskian L x u1 u2 = 1) {c d : ℝ}
    (hc : c ∈ L.I) (hd : d ∈ L.I) (hcd : c < d) :
    gram L c d u1 u1 * gram L c d u2 u2 - gram L c d u1 u2 * gram L c d u2 u1 ≠ 0 := by
  intro hD
  have hu1 := sol_contOn L h1
  have hu2 := sol_contOn L h2
  have key : ∀ a1 a2 : ℂ, gram L c d (fun x => a1 * u1 x + a2 * u2 x)
      (fun x => a1 * u1 x + a2 * u2 x) = 0 → a1 = 0 ∧ a2 = 0 := by
    intro a1 a2 h
    exact indep_on_interval L h1 h2 hW hc hd hcd a1 a2
      (zero_of_gram L ((continuousOn_const.mul hu1).add (continuousOn_const.mul hu2))
        hc hd hcd h)
  by_cases h11 : gram L c d u1 u1 = 0
  · have := key 1 0 (by rw [gram_quad L hu1 hu2 hc hd hcd.le, h11]; simp)
    exact one_ne_zero this.1
  · have := key (gram L c d u1 u2) (-gram L c d u1 u1) (by
      rw [gram_quad L hu1 hu2 hc hd hcd.le]
      simp only [map_neg]
      linear_combination (starRingEnd ℂ (gram L c d u1 u1)) * hD)
    exact h11 (neg_eq_zero.mp this.2)

theorem int_zero_of_le (L : SLData) {f φ : ℝ → ℂ} {c d x : ℝ} (hx : x ≤ c) :
    ∫ y in c..x, f y * (Ioc c d).indicator φ y * (L.r y : ℂ) = 0 := by
  rw [← intervalIntegral.integral_zero (a := c) (b := x) (μ := volume) (E := ℂ)]
  refine intervalIntegral.integral_congr (fun y hy => ?_)
  rw [uIcc_of_ge hx] at hy
  have : y ∉ Ioc c d := fun h => absurd (h.1.trans_le hy.2) (lt_irrefl _)
  simp [indicator_of_notMem this]

theorem int_tail_zero (L : SLData) {f φ : ℝ → ℂ} {c d x : ℝ} (hx : d ≤ x) :
    ∫ y in d..x, f y * (Ioc c d).indicator φ y * (L.r y : ℂ) = 0 := by
  rw [intervalIntegral.integral_of_le hx]
  refine setIntegral_eq_zero_of_forall_eq_zero (fun y hy => ?_)
  have : y ∉ Ioc c d := fun h => absurd (hy.1.trans_le h.2) (lt_irrefl _)
  simp [indicator_of_notMem this]

/-- Gluing: a solution of `(τ - z) v = g` with `g` supported in `(c, d]` which is a prescribed
combination of a fundamental system left of `c` and another one right of `d`. -/
theorem glue (L : SLData) (z : ℂ) {u1 u2 : ℝ → ℂ} (h1 : IsSolution L z 0 u1)
    (h2 : IsSolution L z 0 u2) (hW : ∀ x ∈ L.I, wronskian L x u1 u2 = 1) {c d : ℝ}
    (hc : c ∈ L.I) (hd : d ∈ L.I) (hcd : c < d) (α0 β0 P1 P2 : ℂ) :
    ∃ φ v : ℝ → ℂ, ContinuousOn φ L.I ∧ IsSolution L z ((Ioc c d).indicator φ) v ∧
      (∀ x ∈ L.I, x ≤ c → v x = α0 * u1 x + β0 * u2 x ∧
        quasiDeriv L v x = α0 * quasiDeriv L u1 x + β0 * quasiDeriv L u2 x) ∧
      (∀ x ∈ L.I, d ≤ x → v x = (α0 + P2) * u1 x + (β0 - P1) * u2 x ∧
        quasiDeriv L v x = (α0 + P2) * quasiDeriv L u1 x + (β0 - P1) * quasiDeriv L u2 x) := by
  have hu1 := sol_contOn L h1
  have hu2 := sol_contOn L h2
  have hD := gram_ne L h1 h2 hW hc hd hcd
  set G11 := gram L c d u1 u1
  set G12 := gram L c d u1 u2
  set G21 := gram L c d u2 u1
  set G22 := gram L c d u2 u2
  set D := G11 * G22 - G12 * G21 with hDdef
  set γ1 := (P1 * G22 - P2 * G21) / D
  set γ2 := (P2 * G11 - P1 * G12) / D
  set φ : ℝ → ℂ := fun x => γ1 * starRingEnd ℂ (u1 x) + γ2 * starRingEnd ℂ (u2 x) with hφ
  have hφc : ContinuousOn φ L.I :=
    (continuousOn_const.mul (Complex.continuous_conj.comp_continuousOn hu1)).add
      (continuousOn_const.mul (Complex.continuous_conj.comp_continuousOn hu2))
  set g := (Ioc c d).indicator φ with hgdef
  have hg : LocallyIntegrableOn (fun x => (L.r x : ℂ) * g x) L.I := by
    have e : (fun x => (L.r x : ℂ) * g x) = (Ioc c d).indicator (fun x => φ x * (L.r x : ℂ)) := by
      funext x
      by_cases hx : x ∈ Ioc c d
      · simp [hgdef, indicator_of_mem hx, mul_comm]
      · simp [hgdef, indicator_of_notMem hx]
    rw [e]
    exact ((integrable_indicator_iff measurableSet_Ioc).mpr
      (intOn_Ioc L hφc hc hd hcd.le)).locallyIntegrable.locallyIntegrableOn _
  obtain ⟨F, hF, -, -⟩ := IvpAux.ivp L g hg c hc (α0 * u1 c + β0 * u2 c)
    (α0 * quasiDeriv L u1 c + β0 * quasiDeriv L u2 c)
  obtain ⟨hv, hvc, hvqc⟩ := hF z
  obtain ⟨α, β, hvoc⟩ := voc L z g u1 u2 h1 h2 hW c hc (F z) hv
  have ec := hvoc c hc
  simp only [intervalIntegral.integral_same, add_zero, sub_zero] at ec
  have hWc := hW c hc
  unfold wronskian at hWc
  have E1 : (α - α0) * u1 c + (β - β0) * u2 c = 0 := by linear_combination -ec.1 + hvc
  have E2 : (α - α0) * quasiDeriv L u1 c + (β - β0) * quasiDeriv L u2 c = 0 := by
    linear_combination -ec.2 + hvqc
  have hα : α = α0 := by
    linear_combination quasiDeriv L u2 c * E1 - u2 c * E2 - (α - α0) * hWc
  have hβ : β = β0 := by
    linear_combination u1 c * E2 - quasiDeriv L u1 c * E1 - (β - β0) * hWc
  -- the integrals over `(c, d]`
  have hloc : ∀ {f : ℝ → ℂ}, ContinuousOn f L.I →
      LocallyIntegrableOn (fun y => f y * g y * (L.r y : ℂ)) L.I := by
    intro f hf
    have e : (fun y => f y * g y * (L.r y : ℂ)) = fun y => f y * ((L.r y : ℂ) * g y) := by
      funext y; ring
    rw [e]
    exact hg.continuousOn_mul hf (I_lc L)
  have hcd_int : ∀ {f : ℝ → ℂ}, ContinuousOn f L.I →
      ∫ y in c..d, f y * g y * (L.r y : ℂ) =
        γ1 * gram L c d u1 f + γ2 * gram L c d u2 f := by
    intro f hf
    rw [intervalIntegral.integral_of_le hcd.le]
    have e : ∫ y in Ioc c d, f y * g y * (L.r y : ℂ) =
        ∫ y in Ioc c d, (γ1 * (starRingEnd ℂ (u1 y) * f y * (L.r y : ℂ)) +
          γ2 * (starRingEnd ℂ (u2 y) * f y * (L.r y : ℂ))) := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun y hy => ?_)
      simp only [hgdef, indicator_of_mem hy, hφ]
      ring
    rw [e, integral_add ((gram_int L hu1 hf hc hd hcd.le).const_mul γ1)
      ((gram_int L hu2 hf hc hd hcd.le).const_mul γ2), integral_const_mul, integral_const_mul]
    rfl
  have hI1 : ∫ y in c..d, u1 y * g y * (L.r y : ℂ) = P1 := by
    rw [hcd_int hu1]
    simp only [γ1, γ2]
    field_simp
    ring
  have hI2 : ∫ y in c..d, u2 y * g y * (L.r y : ℂ) = P2 := by
    rw [hcd_int hu2]
    simp only [γ1, γ2]
    field_simp
    ring
  have htail : ∀ {f : ℝ → ℂ}, ContinuousOn f L.I → ∀ x ∈ L.I, d ≤ x →
      ∫ y in c..x, f y * g y * (L.r y : ℂ) = ∫ y in c..d, f y * g y * (L.r y : ℂ) := by
    intro f hf x hx hdx
    rw [← intervalIntegral.integral_add_adjacent_intervals (ii_of_loc L (hloc hf) hc hd)
      (ii_of_loc L (hloc hf) hd hx), int_tail_zero L hdx, add_zero]
  refine ⟨φ, F z, hφc, hv, fun x hx hxc => ?_, fun x hx hdx => ?_⟩
  · have e := hvoc x hx
    rw [int_zero_of_le L hxc, int_zero_of_le L hxc, hα, hβ] at e
    constructor
    · rw [e.1]; ring
    · rw [e.2]; ring
  · have e := hvoc x hx
    rw [htail hu1 x hx hdx, htail hu2 x hx hdx, hI1, hI2, hα, hβ] at e
    constructor
    · rw [e.1]; ring
    · rw [e.2]; ring

end WeylAux


open MeasureTheory Set Filter Topology
open scoped Interval

namespace WeylAux

open TeschlQM.SturmLiouville VoCAux LagAux IvpAux

theorem measure_restrict_eq (L : SLData) {S : Set ℝ} (hS : MeasurableSet S) (hSI : S ⊆ L.I) :
    L.measure.restrict S =
      (volume.restrict S).withDensity (fun x => ENNReal.ofReal (L.r x)) := by
  unfold SLData.measure
  rw [restrict_withDensity hS, Measure.restrict_restrict hS, inter_eq_left.mpr hSI]

theorem ae_measure_of_forall (L : SLData) {P : ℝ → Prop} (h : ∀ x ∈ L.I, P x) :
    ∀ᵐ x ∂L.measure, P x := by
  unfold SLData.measure
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_of_forall_mem (I_isOpen L).measurableSet h)

/-- Gluing of weighted `L²` pieces. -/
theorem memLp_glue (L : SLData) {f : ℝ → ℂ} {S1 S2 : Set ℝ} (hS1 : MeasurableSet S1)
    (hS2 : MeasurableSet S2) (h1 : S1 ⊆ L.I) (h2 : S2 ⊆ L.I)
    (hf1 : MemLp f 2 ((volume.restrict S1).withDensity (fun x => ENNReal.ofReal (L.r x))))
    (hf2 : MemLp f 2 ((volume.restrict S2).withDensity (fun x => ENNReal.ofReal (L.r x))))
    (hz : ∀ x ∈ L.I, x ∉ S1 → x ∉ S2 → f x = 0) : MemLp f 2 L.measure := by
  have hS3 : MeasurableSet (S2 \ S1) := hS2.diff hS1
  have m1 : MemLp (S1.indicator f) 2 L.measure := by
    rw [memLp_indicator_iff_restrict hS1, measure_restrict_eq L hS1 h1]; exact hf1
  have m2 : MemLp ((S2 \ S1).indicator f) 2 L.measure := by
    rw [memLp_indicator_iff_restrict hS3, measure_restrict_eq L hS3 (diff_subset.trans h2)]
    exact memLp_mono_set L hS3 diff_subset hf2
  refine (m1.add m2).ae_eq (ae_measure_of_forall L (fun x hx => ?_))
  by_cases hx1 : x ∈ S1
  · have : x ∉ S2 \ S1 := fun h => h.2 hx1
    simp [indicator_of_mem hx1, indicator_of_notMem this]
  · by_cases hx2 : x ∈ S2
    · have : x ∈ S2 \ S1 := ⟨hx2, hx1⟩
      simp [indicator_of_notMem hx1, indicator_of_mem this]
    · have : x ∉ S2 \ S1 := fun h => hx2 h.1
      simp [indicator_of_notMem hx1, indicator_of_notMem this, hz x hx hx1 hx2]

/-- Bounded measurable functions are weighted-`L²` on compact subintervals of `I`. -/
theorem memLp_of_bdd (L : SLData) {c d : ℝ} (hc : c ∈ L.I) (hd : d ∈ L.I) (hcd : c ≤ d)
    {f : ℝ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict (Icc c d))) {M : ℝ}
    (hM : ∀ x ∈ Icc c d, ‖f x‖ ≤ M) :
    MemLp f 2 ((volume.restrict (Icc c d)).withDensity (fun x => ENNReal.ofReal (L.r x))) := by
  have hsub : Icc c d ⊆ L.I := by rw [← uIcc_of_le hcd]; exact uIcc_subset_I L hc hd
  have hr : IntegrableOn L.r (Icc c d) := L.r_loc.integrableOn_compact_subset hsub isCompact_Icc
  haveI := isFiniteMeasure_withDensity_ofReal hr.2
  refine MemLp.of_bound (hf.mono_ac (withDensity_absolutelyContinuous _ _)) M ?_
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_of_forall_mem measurableSet_Icc hM)

theorem memLp_of_contOn (L : SLData) {c d : ℝ} (hc : c ∈ L.I) (hd : d ∈ L.I) (hcd : c ≤ d)
    {f : ℝ → ℂ} (hf : ContinuousOn f L.I) :
    MemLp f 2 ((volume.restrict (Icc c d)).withDensity (fun x => ENNReal.ofReal (L.r x))) := by
  have hsub : Icc c d ⊆ L.I := by rw [← uIcc_of_le hcd]; exact uIcc_subset_I L hc hd
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hf.mono hsub)
  exact memLp_of_bdd L hc hd hcd ((hf.mono hsub).aestronglyMeasurable measurableSet_Icc) hM

theorem wronskianLeft_of_eventually (L : SLData) {f g : ℝ → ℂ} {K : ℂ}
    (h : ∀ᶠ x in L.atLeft, wronskian L x f g = K) : wronskianLeft L f g = K :=
  (tendsto_const_nhds.congr' (h.mono fun _ hx => hx.symm)).limUnder_eq

theorem wronskianRight_of_eventually (L : SLData) {f g : ℝ → ℂ} {K : ℂ}
    (h : ∀ᶠ x in L.atRight, wronskian L x f g = K) : wronskianRight L f g = K :=
  (tendsto_const_nhds.congr' (h.mono fun _ hx => hx.symm)).limUnder_eq

/-- `W(ū, u)` is constant for a solution of `(τ - λ) u = 0` with real `λ`. -/
theorem wronskian_conj_const (L : SLData) (lam : ℝ) {u : ℝ → ℂ}
    (hu : IsSolution L (lam : ℂ) 0 u) {c x : ℝ} (hc : c ∈ L.I) (hx : x ∈ L.I) :
    wronskian L x (fun y => starRingEnd ℂ (u y)) u =
      wronskian L c (fun y => starRingEnd ℂ (u y)) u := by
  have hd := wronskian_diff L hu (solvesTau_conj L hu) hc hx
  have e : ∫ t in c..x, (L.r t : ℂ) * ((fun x => starRingEnd ℂ ((lam : ℂ) * u x + (0 : ℝ → ℂ) x)) t
      * u t - starRingEnd ℂ (u t) * ((lam : ℂ) * u t + (0 : ℝ → ℂ) t)) = 0 := by
    rw [← intervalIntegral.integral_zero (a := c) (b := x) (μ := volume) (E := ℂ)]
    congr 1; funext t
    simp only [Pi.zero_apply, add_zero, map_mul, Complex.conj_ofReal]
    ring
  rw [e, sub_eq_zero] at hd
  exact hd

end WeylAux


open MeasureTheory Set Filter Topology
open scoped Interval

namespace WeylAux

open TeschlQM.SturmLiouville VoCAux LagAux IvpAux

theorem fund_system' (L : SLData) (z : ℂ) :
    ∃ c0 ∈ L.I, ∃ u₁ u₂ : ℝ → ℂ, IsSolution L z 0 u₁ ∧ IsSolution L z 0 u₂ ∧
      (∀ x ∈ L.I, wronskian L x u₁ u₂ = 1) ∧ u₁ c0 = 1 ∧ quasiDeriv L u₁ c0 = 0 ∧
      u₂ c0 = 0 ∧ quasiDeriv L u₂ c0 = 1 := by
  obtain ⟨c, hc⟩ := exists_mem_I L
  obtain ⟨F1, hF1, -, -⟩ := IvpAux.ivp L 0 (zero_loc L) c hc 1 0
  obtain ⟨F2, hF2, -, -⟩ := IvpAux.ivp L 0 (zero_loc L) c hc 0 1
  obtain ⟨h1, h1a, h1b⟩ := hF1 z
  obtain ⟨h2, h2a, h2b⟩ := hF2 z
  refine ⟨c, hc, F1 z, F2 z, h1, h2, fun x hx => ?_, h1a, h1b, h2a, h2b⟩
  have hd := wronskian_diff L h2 h1 hc hx
  have e : ∫ t in c..x, (L.r t : ℂ) * ((z * F1 z t + (0 : ℝ → ℂ) t) * F2 z t -
      F1 z t * (z * F2 z t + (0 : ℝ → ℂ) t)) = 0 := by
    rw [← intervalIntegral.integral_zero]
    congr 1; funext t; simp only [Pi.zero_apply, add_zero]; ring
  rw [e, sub_eq_zero] at hd
  rw [hd]
  unfold wronskian
  rw [h1a, h1b, h2a, h2b]; ring

theorem inMax_of_pieces (L : SLData) {lam : ℂ} {v φ u1 u2 : ℝ → ℂ} {c d : ℝ} (hc : c ∈ L.I)
    (hd : d ∈ L.I) (hcd : c ≤ d) {S1 : Set ℝ} (hS1 : MeasurableSet S1) (hS1I : S1 ⊆ L.I)
    (hv : IsSolution L lam ((Ioc c d).indicator φ) v) (hφ : ContinuousOn φ L.I) (A B : ℂ)
    (m1 : MemLp u1 2 ((volume.restrict S1).withDensity (fun x => ENNReal.ofReal (L.r x))))
    (m2 : MemLp u2 2 ((volume.restrict S1).withDensity (fun x => ENNReal.ofReal (L.r x))))
    (hS1v : ∀ x ∈ S1, v x = A * u1 x + B * u2 x) (hS1g : ∀ x ∈ S1, x ∉ Ioc c d)
    (hzero : ∀ x ∈ L.I, x ∉ S1 → x ∉ Icc c d → v x = 0 ∧ x ∉ Ioc c d) :
    InMaxDomain L v := by
  have hvc := sol_contOn L hv
  have hsub : Icc c d ⊆ L.I := by rw [← uIcc_of_le hcd]; exact uIcc_subset_I L hc hd
  have hAB : MemLp (fun x => A * u1 x + B * u2 x) 2
      ((volume.restrict S1).withDensity (fun x => ENNReal.ofReal (L.r x))) :=
    (m1.const_mul A).add (m2.const_mul B)
  have hv1 : MemLp v 2 ((volume.restrict S1).withDensity (fun x => ENNReal.ofReal (L.r x))) :=
    hAB.ae_eq ((withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_of_forall_mem hS1 (fun x hx => (hS1v x hx).symm)))
  refine ⟨memLp_glue L hS1 measurableSet_Icc hS1I hsub hv1 (memLp_of_contOn L hc hd hcd hvc)
    (fun x hx h1 h2 => (hzero x hx h1 h2).1), fun x => lam * v x + (Ioc c d).indicator φ x,
    hv, ?_⟩
  refine memLp_glue L hS1 measurableSet_Icc hS1I hsub ?_ ?_ ?_
  · refine (hv1.const_mul lam).ae_eq ((withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_of_forall_mem hS1 (fun x hx => ?_)))
    simp [indicator_of_notMem (hS1g x hx)]
  · obtain ⟨Mv, hMv⟩ := isCompact_Icc.exists_bound_of_continuousOn (hvc.mono hsub)
    obtain ⟨Mφ, hMφ⟩ := isCompact_Icc.exists_bound_of_continuousOn (hφ.mono hsub)
    refine memLp_of_bdd L hc hd hcd ((((hvc.mono hsub).aestronglyMeasurable
      measurableSet_Icc).const_mul lam).add (((hφ.mono hsub).aestronglyMeasurable
      measurableSet_Icc).indicator measurableSet_Ioc)) (M := ‖lam‖ * Mv + Mφ) (fun x hx => ?_)
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hMv x hx) (norm_nonneg _)
    · exact (norm_indicator_le_norm_self _ _).trans (hMφ x hx)
  · intro x hx h1 h2
    obtain ⟨e1, e2⟩ := hzero x hx h1 h2
    simp [e1, indicator_of_notMem e2]

theorem limitCircleLeft_of_sq (L : SLData) (lam : ℝ)
    (H : ∀ u : ℝ → ℂ, IsSolution L lam 0 u → IsSqIntegrableNearLeft L u) :
    IsLimitCircleLeft L := by
  obtain ⟨c0, hc0, u1, u2, h1, h2, hW, d1, d2, d3, d4⟩ := fund_system' L (lam : ℂ)
  obtain ⟨c1, hc1, m1⟩ := H u1 h1
  obtain ⟨c2, hc2, m2⟩ := H u2 h2
  set c := min c1 c2 with hcdef
  have hc : c ∈ L.I := by rcases min_choice c1 c2 with h | h <;> rw [hcdef, h] <;> assumption
  have s1 : {x : ℝ | L.a < (x : EReal) ∧ x < c} ⊆ {x : ℝ | L.a < (x : EReal) ∧ x < c1} :=
    fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_left _ _)⟩
  have s2 : {x : ℝ | L.a < (x : EReal) ∧ x < c} ⊆ {x : ℝ | L.a < (x : EReal) ∧ x < c2} :=
    fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_right _ _)⟩
  have m1' := memLp_mono_set L (measSL L c) s1 m1
  have m2' := memLp_mono_set L (measSL L c) s2 m2
  obtain ⟨-, d, -, hcd, -, hd⟩ := exists_Icc_subset_I L hc
  obtain ⟨φ1, v1, hφ1, hv1, hl1, hr1⟩ := glue L (lam : ℂ) h1 h2 hW hc hd hcd 1 0 0 (-1)
  obtain ⟨φ2, v2, hφ2, hv2, hl2, hr2⟩ := glue L (lam : ℂ) h1 h2 hW hc hd hcd 0 1 1 0
  have hz : ∀ x ∈ L.I, x ∉ {x : ℝ | L.a < (x : EReal) ∧ x < c} → x ∉ Icc c d → d < x := by
    intro x hx h1 h2
    have hcx : c ≤ x := by
      by_contra h; exact h1 ⟨hx.1, not_le.mp h⟩
    by_contra h; exact h2 ⟨hcx, not_lt.mp h⟩
  have hg : ∀ x ∈ {x : ℝ | L.a < (x : EReal) ∧ x < c}, x ∉ Ioc c d :=
    fun x hx h => absurd (hx.2.trans h.1) (lt_irrefl _)
  have hmax1 : InMaxDomain L v1 := inMax_of_pieces L hc hd hcd.le (measSL L c) (SL_sub L hc)
    hv1 hφ1 1 0 m1' m2' (fun x hx => (hl1 x (SL_sub L hc hx) hx.2.le).1) hg
    (fun x hx h1 h2 => by
      have hdx := hz x hx h1 h2
      refine ⟨by rw [(hr1 x hx hdx.le).1]; ring, fun h => absurd (h.2.trans_lt hdx) (lt_irrefl _)⟩)
  have hmax2 : InMaxDomain L v2 := inMax_of_pieces L hc hd hcd.le (measSL L c) (SL_sub L hc)
    hv2 hφ2 0 1 m1' m2' (fun x hx => (hl2 x (SL_sub L hc hx) hx.2.le).1) hg
    (fun x hx h1 h2 => by
      have hdx := hz x hx h1 h2
      refine ⟨by rw [(hr2 x hx hdx.le).1]; ring, fun h => absurd (h.2.trans_lt hdx) (lt_irrefl _)⟩)
  have hev : ∀ᶠ x in L.atLeft, x ∈ L.I ∧ x < c :=
    (eventually_mem_left L).and (eventually_lt_left L hc.1)
  refine ⟨v1, hmax1, ?_, v2, hmax2, ?_⟩
  · refine wronskianLeft_of_eventually L (hev.mono fun x ⟨hx, hxc⟩ => ?_)
    have hc1 := quasiDeriv_conj L hv1.1 x hx
    have hcu := quasiDeriv_conj L h1.1 x hx
    have hconst := wronskian_conj_const L lam h1 hc0 hx
    have hqc0 := quasiDeriv_conj L h1.1 c0 hc0
    obtain ⟨e1, e2⟩ := hl1 x hx hxc.le
    unfold wronskian at hconst ⊢
    beta_reduce at hconst ⊢
    rw [hc1, e1, e2]
    rw [hcu, hqc0, d1, d2] at hconst
    simp only [map_one, map_zero, one_mul, mul_zero, zero_mul, sub_zero] at hconst
    simp only [map_add, map_mul, map_one, map_zero, one_mul, zero_mul, add_zero]
    linear_combination hconst
  · rw [wronskianLeft_of_eventually L (K := 1) (hev.mono fun x ⟨hx, hxc⟩ => ?_)]
    · exact one_ne_zero
    obtain ⟨e1, e2⟩ := hl1 x hx hxc.le
    obtain ⟨f1, f2⟩ := hl2 x hx hxc.le
    have := hW x hx
    unfold wronskian at this ⊢
    rw [e1, e2, f1, f2]
    linear_combination this

theorem limitCircleRight_of_sq (L : SLData) (lam : ℝ)
    (H : ∀ u : ℝ → ℂ, IsSolution L lam 0 u → IsSqIntegrableNearRight L u) :
    IsLimitCircleRight L := by
  obtain ⟨c0, hc0, u1, u2, h1, h2, hW, d1, d2, d3, d4⟩ := fund_system' L (lam : ℂ)
  obtain ⟨c1, hc1, m1⟩ := H u1 h1
  obtain ⟨c2, hc2, m2⟩ := H u2 h2
  set d := max c1 c2 with hddef
  have hd : d ∈ L.I := by rcases max_choice c1 c2 with h | h <;> rw [hddef, h] <;> assumption
  have s1 : {x : ℝ | d < x ∧ (x : EReal) < L.b} ⊆ {x : ℝ | c1 < x ∧ (x : EReal) < L.b} :=
    fun x hx => ⟨lt_of_le_of_lt (le_max_left _ _) hx.1, hx.2⟩
  have s2 : {x : ℝ | d < x ∧ (x : EReal) < L.b} ⊆ {x : ℝ | c2 < x ∧ (x : EReal) < L.b} :=
    fun x hx => ⟨lt_of_le_of_lt (le_max_right _ _) hx.1, hx.2⟩
  have m1' := memLp_mono_set L (measSR L d) s1 m1
  have m2' := memLp_mono_set L (measSR L d) s2 m2
  obtain ⟨c, -, hcd, -, hc, -⟩ := exists_Icc_subset_I L hd
  obtain ⟨φ1, v1, hφ1, hv1, hl1, hr1⟩ := glue L (lam : ℂ) h1 h2 hW hc hd hcd 0 0 0 1
  obtain ⟨φ2, v2, hφ2, hv2, hl2, hr2⟩ := glue L (lam : ℂ) h1 h2 hW hc hd hcd 0 0 (-1) 0
  have hz : ∀ x ∈ L.I, x ∉ {x : ℝ | d < x ∧ (x : EReal) < L.b} → x ∉ Icc c d → x < c := by
    intro x hx h1 h2
    have hxd : x ≤ d := by
      by_contra h; exact h1 ⟨not_le.mp h, hx.2⟩
    by_contra h; exact h2 ⟨not_lt.mp h, hxd⟩
  have hg : ∀ x ∈ {x : ℝ | d < x ∧ (x : EReal) < L.b}, x ∉ Ioc c d :=
    fun x hx h => absurd (hx.1.trans_le h.2) (lt_irrefl _)
  have hmax1 : InMaxDomain L v1 := inMax_of_pieces L hc hd hcd.le (measSR L d) (SR_sub L hd)
    hv1 hφ1 1 0 m1' m2' (fun x hx => by rw [(hr1 x (SR_sub L hd hx) hx.1.le).1]; ring) hg
    (fun x hx h1 h2 => by
      have hxc := hz x hx h1 h2
      refine ⟨by rw [(hl1 x hx hxc.le).1]; ring, fun h => absurd (hxc.trans h.1) (lt_irrefl _)⟩)
  have hmax2 : InMaxDomain L v2 := inMax_of_pieces L hc hd hcd.le (measSR L d) (SR_sub L hd)
    hv2 hφ2 0 1 m1' m2' (fun x hx => by rw [(hr2 x (SR_sub L hd hx) hx.1.le).1]; ring) hg
    (fun x hx h1 h2 => by
      have hxc := hz x hx h1 h2
      refine ⟨by rw [(hl2 x hx hxc.le).1]; ring, fun h => absurd (hxc.trans h.1) (lt_irrefl _)⟩)
  have hev : ∀ᶠ x in L.atRight, x ∈ L.I ∧ d < x :=
    (eventually_mem_right L).and (eventually_gt_right L hd.2)
  refine ⟨v1, hmax1, ?_, v2, hmax2, ?_⟩
  · refine wronskianRight_of_eventually L (hev.mono fun x ⟨hx, hxd⟩ => ?_)
    have hc1 := quasiDeriv_conj L hv1.1 x hx
    have hcu := quasiDeriv_conj L h1.1 x hx
    have hconst := wronskian_conj_const L lam h1 hc0 hx
    have hqc0 := quasiDeriv_conj L h1.1 c0 hc0
    have e1 : v1 x = u1 x := by rw [(hr1 x hx hxd.le).1]; ring
    have e2 : quasiDeriv L v1 x = quasiDeriv L u1 x := by rw [(hr1 x hx hxd.le).2]; ring
    unfold wronskian at hconst ⊢
    beta_reduce at hconst ⊢
    rw [hc1, e1, e2]
    rw [hcu, hqc0, d1, d2] at hconst
    simp only [map_zero, mul_zero, zero_mul, sub_zero] at hconst
    exact hconst
  · rw [wronskianRight_of_eventually L (K := 1) (hev.mono fun x ⟨hx, hxd⟩ => ?_)]
    · exact one_ne_zero
    have e1 : v1 x = u1 x := by rw [(hr1 x hx hxd.le).1]; ring
    have e2 : quasiDeriv L v1 x = quasiDeriv L u1 x := by rw [(hr1 x hx hxd.le).2]; ring
    have f1 : v2 x = u2 x := by rw [(hr2 x hx hxd.le).1]; ring
    have f2 : quasiDeriv L v2 x = quasiDeriv L u2 x := by rw [(hr2 x hx hxd.le).2]; ring
    have := hW x hx
    unfold wronskian at this ⊢
    rw [e1, e2, f1, f2]
    exact this

theorem limitCircle_of_sqIntegrable (L : SLData) (lam : ℝ) :
    ((∀ u : ℝ → ℂ, IsSolution L lam 0 u → IsSqIntegrableNearLeft L u) → IsLimitCircleLeft L) ∧
    ((∀ u : ℝ → ℂ, IsSolution L lam 0 u → IsSqIntegrableNearRight L u) →
      IsLimitCircleRight L) :=
  ⟨limitCircleLeft_of_sq L lam, limitCircleRight_of_sq L lam⟩

end WeylAux

end SecBase

section SecBc

open MeasureTheory Set

open TeschlQM.SturmLiouville MeasureTheory Filter Topology

theorem lagrange_identity_aux (L : SLData) (f g F G : ℝ → ℂ)
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
    have : IntegrableOn _ L.I := (LagAux.integrableOn_of_integrable_measure L i2).sub
      (LagAux.integrableOn_of_integrable_measure L i1)
    refine IntegrableOn.congr_fun this (fun t _ => ?_) (LagAux.I_isOpen L).measurableSet
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


open MeasureTheory Set Filter Topology

namespace BcAux

open TeschlQM.SturmLiouville

theorem conj_conj_fun (h : ℝ → ℂ) : (fun x => starRingEnd ℂ ((fun y => starRingEnd ℂ (h y)) x)) = h := by
  funext x; simp

theorem maxDomain_conj (L : SLData) {h : ℝ → ℂ} (hh : InMaxDomain L h) :
    InMaxDomain L (fun x => starRingEnd ℂ (h x)) := by
  obtain ⟨h2, H, hH, hH2⟩ := hh
  exact ⟨h2.star, _, LagAux.solvesTau_conj L hH, hH2.star⟩

theorem tendsto_W (L : SLData) {f g : ℝ → ℂ} (hf : InMaxDomain L f) (hg : InMaxDomain L g) :
    Tendsto (fun x => wronskian L x g f) L.atLeft (𝓝 (wronskianLeft L g f)) := by
  obtain ⟨hgc2, G, hG, hG2⟩ := maxDomain_conj L hg
  obtain ⟨hf2, F, hF, hF2⟩ := hf
  have := (lagrange_identity_aux L f (fun x => starRingEnd ℂ (g x)) F G hf2 hgc2 hF hG hF2 hG2).1
  rw [conj_conj_fun] at this
  exact this

theorem W_conj_left (L : SLData) {f g : ℝ → ℂ} (hf : InMaxDomain L f) (hg : InMaxDomain L g) :
    wronskianLeft L (fun x => starRingEnd ℂ (g x)) (fun x => starRingEnd ℂ (f x)) =
      starRingEnd ℂ (wronskianLeft L g f) := by
  have t1 := tendsto_W L (maxDomain_conj L hf) (maxDomain_conj L hg)
  have t2 := (Complex.continuous_conj.tendsto _).comp (tendsto_W L hf hg)
  refine tendsto_nhds_unique t1 (t2.congr' ?_)
  filter_upwards [LagAux.eventually_mem_left L] with x hx
  obtain ⟨-, F, hF, -⟩ := hf
  obtain ⟨-, G, hG, -⟩ := hg
  simp only [Function.comp, wronskian]
  rw [LagAux.quasiDeriv_conj L hF.1 x hx, LagAux.quasiDeriv_conj L hG.1 x hx]
  simp

theorem W_anti_left (L : SLData) {f g : ℝ → ℂ} (hf : InMaxDomain L f) (hg : InMaxDomain L g) :
    wronskianLeft L g f = -wronskianLeft L f g := by
  have t1 := tendsto_W L hf hg
  have t2 := (tendsto_W L hg hf).neg
  refine tendsto_nhds_unique t1 (t2.congr' (Eventually.of_forall fun x => ?_))
  simp only [wronskian]; ring

theorem plucker_left (L : SLData) {f1 f2 f3 f4 : ℝ → ℂ} (h1 : InMaxDomain L f1)
    (h2 : InMaxDomain L f2) (h3 : InMaxDomain L f3) (h4 : InMaxDomain L f4) :
    wronskianLeft L f1 f2 * wronskianLeft L f3 f4 + wronskianLeft L f1 f3 * wronskianLeft L f4 f2 +
      wronskianLeft L f1 f4 * wronskianLeft L f2 f3 = 0 := by
  have t := (((tendsto_W L h2 h1).mul (tendsto_W L h4 h3)).add
    ((tendsto_W L h3 h1).mul (tendsto_W L h2 h4))).add
    ((tendsto_W L h4 h1).mul (tendsto_W L h3 h2))
  refine tendsto_nhds_unique t (tendsto_const_nhds.congr' (Eventually.of_forall fun x => ?_))
  simp only [wronskian]; ring

end BcAux

open TeschlQM.SturmLiouville

theorem BcAux.wronskian_bc_symmetric (L : SLData) (v fhat : ℝ → ℂ) (hv : InMaxDomain L v)
    (hvv : wronskianLeft L (fun x => starRingEnd ℂ (v x)) v = 0)
    (hfhat : InMaxDomain L fhat)
    (hne : wronskianLeft L (fun x => starRingEnd ℂ (v x)) fhat ≠ 0)
    (f g : ℝ → ℂ) (hf : InMaxDomain L f) (hg : InMaxDomain L g) :
    (wronskianLeft L v f = 0 ↔ wronskianLeft L v (fun x => starRingEnd ℂ (f x)) = 0) ∧
      (wronskianLeft L v f = 0 → wronskianLeft L v g = 0 →
        wronskianLeft L (fun x => starRingEnd ℂ (g x)) f = 0) := by
  have hvc := BcAux.maxDomain_conj L hv
  have hvv' : wronskianLeft L v (fun x => starRingEnd ℂ (v x)) = 0 := by
    rw [BcAux.W_anti_left L hvc hv, hvv, neg_zero]
  -- `W_a(v, f̂) ≠ 0`
  have hvf : wronskianLeft L v fhat ≠ 0 := by
    intro h0
    have hfc := BcAux.maxDomain_conj L hfhat
    have P := BcAux.plucker_left L hv hfc hvc hfhat
    rw [hvv', h0] at P
    simp only [zero_mul, add_zero] at P
    rcases mul_eq_zero.mp P with h | h
    · have := BcAux.W_conj_left L hfc hv
      rw [BcAux.conj_conj_fun, h, map_zero] at this
      exact hne this
    · exact hne h
  -- forward direction of (9.15), in the form `W_a(v, h) = 0 → W_a(v*, h) = 0`
  have fwd : ∀ h : ℝ → ℂ, InMaxDomain L h → wronskianLeft L v h = 0 →
      wronskianLeft L (fun x => starRingEnd ℂ (v x)) h = 0 := by
    intro h hh h0
    have P := BcAux.plucker_left L hv hh hvc hfhat
    rw [h0, hvv'] at P
    simp only [zero_mul, add_zero, zero_add] at P
    rcases mul_eq_zero.mp P with h1 | h1
    · exact absurd h1 hvf
    · rw [BcAux.W_anti_left L hh hvc, h1, neg_zero]
  have fwd' : ∀ h : ℝ → ℂ, InMaxDomain L h → wronskianLeft L v h = 0 →
      wronskianLeft L v (fun x => starRingEnd ℂ (h x)) = 0 := by
    intro h hh h0
    have := BcAux.W_conj_left L hh hvc
    rw [BcAux.conj_conj_fun, fwd h hh h0, map_zero] at this
    exact this
  refine ⟨⟨fwd' f hf, fun h0 => ?_⟩, fun h1 h2 => ?_⟩
  · have := fwd' _ (BcAux.maxDomain_conj L hf) h0
    rwa [BcAux.conj_conj_fun] at this
  · have hgc := BcAux.maxDomain_conj L hg
    have P := BcAux.plucker_left L hv hfhat hf hgc
    rw [h1, fwd' g hg h2] at P
    simp only [zero_mul, add_zero, zero_mul] at P
    rcases mul_eq_zero.mp P with h3 | h3
    · exact absurd h3 hvf
    · rw [BcAux.W_anti_left L hf hgc, h3, neg_zero]

end SecBc

section SecLP1

open MeasureTheory Set Filter Topology
open scoped Interval

namespace WeylLP

open TeschlQM.SturmLiouville VoCAux LagAux IvpAux WeylAux

theorem locInt_lin {f g : ℝ → ℂ} {S : Set ℝ} (hf : LocallyIntegrableOn f S)
    (hg : LocallyIntegrableOn g S) (a b : ℂ) :
    LocallyIntegrableOn (fun x => a * f x + b * g x) S := by
  have h1 : LocallyIntegrableOn (fun x => a * f x) S :=
    fun x hx => (hf x hx).imp fun _ ht => ⟨ht.1, ht.2.const_mul a⟩
  have h2 : LocallyIntegrableOn (fun x => b * g x) S :=
    fun x hx => (hg x hx).imp fun _ ht => ⟨ht.1, ht.2.const_mul b⟩
  exact h1.add h2

theorem integral_lin (L : SLData) {f g : ℝ → ℂ} (hf : LocallyIntegrableOn f L.I)
    (hg : LocallyIntegrableOn g L.I) (a b : ℂ) {x y : ℝ} (hx : x ∈ L.I) (hy : y ∈ L.I) :
    ∫ t in x..y, (a * f t + b * g t) = a * (∫ t in x..y, f t) + b * (∫ t in x..y, g t) := by
  rw [intervalIntegral.integral_add ((ii_of_loc L hf hx hy).const_mul a)
    ((ii_of_loc L hg hx hy).const_mul b), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

theorem isQD_lin (L : SLData) {f1 f2 g1 g2 : ℝ → ℂ} (h1 : IsQuasiDerivative L f1 g1)
    (h2 : IsQuasiDerivative L f2 g2) (a b : ℂ) :
    IsQuasiDerivative L (fun x => a * f1 x + b * f2 x) (fun x => a * g1 x + b * g2 x) := by
  obtain ⟨⟨k1, hk1, hp1⟩, hl1, hq1⟩ := h1
  obtain ⟨⟨k2, hk2, hp2⟩, hl2, hq2⟩ := h2
  refine ⟨⟨fun x => a * k1 x + b * k2 x, locInt_lin hk1 hk2 a b, fun x hx y hy => ?_⟩, ?_, ?_⟩
  · rw [integral_lin L hk1 hk2 a b hx hy]
    beta_reduce
    linear_combination a * hp1 x hx y hy + b * hp2 x hx y hy
  · have e : (fun t => (a * g1 t + b * g2 t) / (L.p t : ℂ)) =
        fun t => a * (g1 t / (L.p t : ℂ)) + b * (g2 t / (L.p t : ℂ)) := by
      funext t; ring
    rw [e]; exact locInt_lin hl1 hl2 a b
  · intro x hx y hy
    have e : (fun t => (a * g1 t + b * g2 t) / (L.p t : ℂ)) =
        fun t => a * (g1 t / (L.p t : ℂ)) + b * (g2 t / (L.p t : ℂ)) := by
      funext t; ring
    rw [e, integral_lin L hl1 hl2 a b hx hy]
    beta_reduce
    linear_combination a * hq1 x hx y hy + b * hq2 x hx y hy

/-- Linear combinations of solutions of `τ f = G`. -/
theorem solvesTau_lin (L : SLData) {f1 f2 G1 G2 : ℝ → ℂ} (h1 : SolvesTau L f1 G1)
    (h2 : SolvesTau L f2 G2) (a b : ℂ) :
    SolvesTau L (fun x => a * f1 x + b * f2 x) (fun x => a * G1 x + b * G2 x) ∧
      ∀ x ∈ L.I, quasiDeriv L (fun x => a * f1 x + b * f2 x) x =
        a * quasiDeriv L f1 x + b * quasiDeriv L f2 x := by
  obtain ⟨hq1, hl1, hp1⟩ := h1
  obtain ⟨hq2, hl2, hp2⟩ := h2
  have hQ := isQD_lin L hq1 hq2 a b
  have hU := qd_unique L (isQD_quasiDeriv L hQ) hQ
  refine ⟨⟨isQD_quasiDeriv L hQ, ?_, ?_⟩, hU⟩
  · have e : (fun t => (L.q t : ℂ) * (a * f1 t + b * f2 t) - (L.r t : ℂ) * (a * G1 t + b * G2 t))
        = fun t => a * ((L.q t : ℂ) * f1 t - (L.r t : ℂ) * G1 t) +
          b * ((L.q t : ℂ) * f2 t - (L.r t : ℂ) * G2 t) := by
      funext t; ring
    rw [e]; exact locInt_lin hl1 hl2 a b
  · intro x hx y hy
    have e : (fun t => (L.q t : ℂ) * (a * f1 t + b * f2 t) - (L.r t : ℂ) * (a * G1 t + b * G2 t))
        = fun t => a * ((L.q t : ℂ) * f1 t - (L.r t : ℂ) * G1 t) +
          b * ((L.q t : ℂ) * f2 t - (L.r t : ℂ) * G2 t) := by
      funext t; ring
    rw [hU y hy, hU x hx, e, integral_lin L hl1 hl2 a b hx hy]
    linear_combination a * hp1 x hx y hy + b * hp2 x hx y hy

/-- Linear combinations of solutions of `(τ − z) f = g`. -/
theorem isSolution_lin (L : SLData) {z : ℂ} {f1 f2 g1 g2 : ℝ → ℂ} (h1 : IsSolution L z g1 f1)
    (h2 : IsSolution L z g2 f2) (a b : ℂ) :
    IsSolution L z (fun x => a * g1 x + b * g2 x) (fun x => a * f1 x + b * f2 x) ∧
      ∀ x ∈ L.I, quasiDeriv L (fun x => a * f1 x + b * f2 x) x =
        a * quasiDeriv L f1 x + b * quasiDeriv L f2 x := by
  obtain ⟨hs, hq⟩ := solvesTau_lin L h1 h2 a b
  refine ⟨?_, hq⟩
  unfold IsSolution
  have e : (fun x => z * (a * f1 x + b * f2 x) + (a * g1 x + b * g2 x)) =
      fun x => a * (z * f1 x + g1 x) + b * (z * f2 x + g2 x) := by
    funext x; ring
  rw [e]; exact hs

/-- `Im (conj(u x) · (p u')(x))`, i.e. `W_x(u*, u) / (2i)`. -/
noncomputable def imW (L : SLData) (u : ℝ → ℂ) (x : ℝ) : ℝ :=
  (starRingEnd ℂ (u x) * quasiDeriv L u x).im

/-- Weighted `L²` mass of `u` between `y` and `c`. -/
noncomputable def Nrm (L : SLData) (u : ℝ → ℂ) (y c : ℝ) : ℝ :=
  ∫ t in Ι y c, L.r t * ‖u t‖ ^ 2

/-- The energy identity: for `(τ − z) G = h`,
`Im(G* pG')(y) − Im(G* pG')(c) = −∫_c^y r (Im z |G|² + Im(G* h))`. -/
theorem energy (L : SLData) {z : ℂ} {h G : ℝ → ℂ} (hG : IsSolution L z h G) {c y : ℝ}
    (hc : c ∈ L.I) (hy : y ∈ L.I) :
    imW L G y - imW L G c =
      -∫ t in c..y, L.r t * (z.im * ‖G t‖ ^ 2 + (starRingEnd ℂ (G t) * h t).im) := by
  have hconj := solvesTau_conj L hG
  have hd := wronskian_diff L hG hconj hc hy
  have hq := quasiDeriv_conj L hG.1
  have key : ∀ x ∈ L.I, wronskian L x (fun t => starRingEnd ℂ (G t)) G =
      (2 * imW L G x : ℝ) * Complex.I := by
    intro x hx
    unfold wronskian imW
    rw [hq x hx]
    apply Complex.ext <;> simp <;> ring
  rw [key y hy, key c hc] at hd
  have aux1 : ∀ u w : ℂ, starRingEnd ℂ w * u - starRingEnd ℂ u * w =
      ((-2 * (starRingEnd ℂ u * w).im : ℝ) : ℂ) * Complex.I := by
    intro u w; apply Complex.ext <;> simp <;> ring
  have aux2 : ∀ u w : ℂ, (starRingEnd ℂ u * (z * u + w)).im =
      z.im * ‖u‖ ^ 2 + (starRingEnd ℂ u * w).im := by
    intro u w
    simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.conj_re,
      Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
    ring
  have aux3 : ∀ a : ℝ, ((a : ℂ) * Complex.I).im = a := by intro a; simp
  have e2 : (fun t => (L.r t : ℂ) * (starRingEnd ℂ (z * G t + h t) * G t -
      starRingEnd ℂ (G t) * (z * G t + h t))) =
      fun t => ((-2 * (L.r t * (z.im * ‖G t‖ ^ 2 + (starRingEnd ℂ (G t) * h t).im)) : ℝ) : ℂ) *
        Complex.I := by
    funext t
    rw [aux1, aux2]
    push_cast; ring
  rw [e2, intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_const_mul] at hd
  have h3 := congrArg Complex.im hd
  rw [Complex.sub_im, aux3, aux3, aux3] at h3
  linarith

end WeylLP

end SecLP1

section SecSA1

/-!
# Basic facts for the self-adjointness theorem (Teschl, Theorem 9.6)
-/

open MeasureTheory Set Filter Topology
open scoped Interval

namespace SAAux

open TeschlQM.SturmLiouville VoCAux LagAux IvpAux WeylAux

theorem tau_contOn (L : SLData) {f G : ℝ → ℂ} (hf : SolvesTau L f G) : ContinuousOn f L.I := by
  obtain ⟨c, hc⟩ := exists_mem_I L
  obtain ⟨⟨-, hl, hp⟩, -, -⟩ := hf
  refine ((continuousOn_const (c := f c)).add (contOn_prim L hl hc)).congr (fun x hx => ?_)
  have := hp c hc x hx
  beta_reduce at this ⊢
  simp only [Pi.add_apply]
  rw [← this]; ring

theorem tau_qd_contOn (L : SLData) {f G : ℝ → ℂ} (hf : SolvesTau L f G) :
    ContinuousOn (quasiDeriv L f) L.I := by
  obtain ⟨c, hc⟩ := exists_mem_I L
  obtain ⟨-, hl, hp⟩ := hf
  refine ((continuousOn_const (c := quasiDeriv L f c)).add (contOn_prim L hl hc)).congr
    (fun x hx => ?_)
  have := hp c hc x hx
  beta_reduce at this ⊢
  simp only [Pi.add_apply]
  rw [← this]; ring

theorem r_ne (L : SLData) {x : ℝ} (hx : x ∈ L.I) : (L.r x : ℂ) ≠ 0 := by
  exact_mod_cast (L.r_pos x hx.1 hx.2).ne'

theorem ae_vol_of_ae (L : SLData) {P : ℝ → Prop} (h : ∀ᵐ x ∂L.measure, P x) :
    ∀ᵐ x ∂(volume.restrict L.I), P x := by
  unfold SLData.measure at h
  rw [ae_withDensity_iff' (r_aemeas L)] at h
  filter_upwards [h, ae_restrict_mem (I_isOpen L).measurableSet] with x hx hxI
  exact hx (by simpa using L.r_pos x hxI.1 hxI.2)

theorem ae_of_ae_vol (L : SLData) {P : ℝ → Prop} (h : ∀ᵐ x ∂(volume.restrict L.I), P x) :
    ∀ᵐ x ∂L.measure, P x := by
  unfold SLData.measure
  exact (withDensity_absolutelyContinuous _ _).ae_le h

theorem eqOn_of_ae (L : SLData) {f g : ℝ → ℂ} (hf : ContinuousOn f L.I)
    (hg : ContinuousOn g L.I) (h : f =ᵐ[L.measure] g) : ∀ x ∈ L.I, f x = g x :=
  fun _ hx => Measure.eqOn_open_of_ae_eq (ae_vol_of_ae L h) (I_isOpen L) hf hg hx

theorem mem_I_of_between (L : SLData) {s t x : ℝ} (hs : s ∈ L.I) (ht : t ∈ L.I) (h1 : s ≤ x)
    (h2 : x ≤ t) : x ∈ L.I :=
  uIcc_subset_I L hs ht (by rw [uIcc_of_le (h1.trans h2)]; exact ⟨h1, h2⟩)

theorem Icc_sub_I (L : SLData) {s t : ℝ} (hs : s ∈ L.I) (ht : t ∈ L.I) : Icc s t ⊆ L.I :=
  fun _ hx => mem_I_of_between L hs ht hx.1 hx.2

/-- A local-to-global principle for almost-everywhere statements on `I`. -/
theorem ae_I_of_local (L : SLData) {P : ℝ → Prop}
    (h : ∀ s t : ℝ, s ∈ L.I → t ∈ L.I → s < t → ∀ᵐ x ∂(volume.restrict (Ioo s t)), P x) :
    ∀ᵐ x ∂(volume.restrict L.I), P x := by
  classical
  set S : ℚ × ℚ → Set ℝ := fun pq =>
    if (pq.1 : ℝ) ∈ L.I ∧ (pq.2 : ℝ) ∈ L.I ∧ (pq.1 : ℝ) < pq.2 then Ioo (pq.1 : ℝ) pq.2 else ∅
  have hI : L.I = ⋃ pq, S pq := by
    ext x
    simp only [mem_iUnion]
    constructor
    · intro hx
      obtain ⟨s, t, hsx, hxt, hs, ht⟩ := exists_Icc_subset_I L hx
      obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn hsx
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hxt
      have hpI : (p : ℝ) ∈ L.I := mem_I_of_between L hs ht hp1.le (hp2.trans hxt).le
      have hqI : (q : ℝ) ∈ L.I := mem_I_of_between L hs ht (hsx.trans hq1).le hq2.le
      refine ⟨(p, q), ?_⟩
      simp only [S, if_pos (⟨hpI, hqI, hp2.trans hq1⟩ : (p : ℝ) ∈ L.I ∧ (q : ℝ) ∈ L.I ∧
        (p : ℝ) < q)]
      exact ⟨hp2, hq1⟩
    · rintro ⟨pq, hpq⟩
      simp only [S] at hpq
      split_ifs at hpq with hc
      · exact mem_I_of_between L hc.1 hc.2.1 hpq.1.le hpq.2.le
      · exact absurd hpq (notMem_empty x)
  rw [hI, ae_restrict_iUnion_iff]
  intro pq
  simp only [S]
  split_ifs with hc
  · exact h _ _ hc.1 hc.2.1 hc.2.2
  · simp

theorem locInt_congr (L : SLData) {f g : ℝ → ℂ} (hf : LocallyIntegrableOn f L.I)
    (e : ∀ᵐ x ∂(volume.restrict L.I), f x = g x) : LocallyIntegrableOn g L.I := by
  rw [locallyIntegrableOn_iff (I_lc L)] at hf ⊢
  intro k hk hkc
  exact (hf k hk hkc).congr_fun_ae (ae_restrict_of_ae_restrict_of_subset hk e)

theorem locInt_congr_on (L : SLData) {f g : ℝ → ℂ} (hf : LocallyIntegrableOn f L.I)
    (e : ∀ x ∈ L.I, f x = g x) : LocallyIntegrableOn g L.I :=
  locInt_congr L hf (ae_restrict_of_forall_mem (I_isOpen L).measurableSet e)

/-! ### Congruence for quasi-derivatives and `SolvesTau` -/

theorem isQD_congr (L : SLData) {f g f1 : ℝ → ℂ} (h : ∀ x ∈ L.I, f x = g x)
    (hf : IsQuasiDerivative L f f1) : IsQuasiDerivative L g f1 :=
  ⟨hf.1, hf.2.1, fun x hx y hy => by rw [← h x hx, ← h y hy]; exact hf.2.2 x hx y hy⟩

theorem quasiDeriv_congr (L : SLData) {f g : ℝ → ℂ} (h : ∀ x ∈ L.I, f x = g x) :
    quasiDeriv L f = quasiDeriv L g := by
  have hP : IsQuasiDerivative L f = IsQuasiDerivative L g :=
    funext fun f1 => propext ⟨isQD_congr L h, isQD_congr L (fun x hx => (h x hx).symm)⟩
  unfold quasiDeriv
  rw [hP]

theorem solvesTau_congr (L : SLData) {f g F : ℝ → ℂ} (h : ∀ x ∈ L.I, f x = g x)
    (hf : SolvesTau L f F) : SolvesTau L g F := by
  obtain ⟨h1, h2, h3⟩ := hf
  rw [quasiDeriv_congr L h] at h1 h3
  refine ⟨isQD_congr L h h1, locInt_congr_on L h2 (fun x hx => by rw [h x hx]),
    fun x hx y hy => ?_⟩
  rw [h3 x hx y hy]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  simp only [h t (uIcc_subset_I L hx hy ht)]

theorem solvesTau_congr_rhs (L : SLData) {f F G : ℝ → ℂ} (h : F =ᵐ[L.measure] G)
    (hf : SolvesTau L f F) : SolvesTau L f G := by
  obtain ⟨h1, h2, h3⟩ := hf
  have hv := ae_vol_of_ae L h
  refine ⟨h1, locInt_congr L h2 (hv.mono fun x hx => by rw [hx]), fun x hx y hy => ?_⟩
  rw [h3 x hx y hy]
  refine intervalIntegral.integral_congr_ae ?_
  have hsub : Ι x y ⊆ L.I := uIoc_subset_uIcc.trans (uIcc_subset_I L hx hy)
  have := (ae_restrict_iff' (I_isOpen L).measurableSet).mp hv
  filter_upwards [this] with t ht htm
  rw [ht (hsub htm)]

theorem isQD_zero (L : SLData) : IsQuasiDerivative L (0 : ℝ → ℂ) (0 : ℝ → ℂ) := by
  refine ⟨⟨0, ?_, fun x _ y _ => by simp⟩, ?_, fun x _ y _ => by simp⟩
  · exact locallyIntegrableOn_zero
  · have : (fun t => (0 : ℝ → ℂ) t / (L.p t : ℂ)) = fun _ => (0 : ℂ) := by funext t; simp
    rw [this]; exact locallyIntegrableOn_zero

theorem quasiDeriv_zero (L : SLData) : ∀ x ∈ L.I, quasiDeriv L (0 : ℝ → ℂ) x = 0 :=
  fun x hx => qd_unique L (isQD_quasiDeriv L (isQD_zero L)) (isQD_zero L) x hx

theorem solvesTau_zero (L : SLData) : SolvesTau L (0 : ℝ → ℂ) (0 : ℝ → ℂ) := by
  refine ⟨isQD_quasiDeriv L (isQD_zero L), ?_, fun x hx y hy => ?_⟩
  · have : (fun t => (L.q t : ℂ) * (0 : ℝ → ℂ) t - (L.r t : ℂ) * (0 : ℝ → ℂ) t) =
        fun _ => (0 : ℂ) := by funext t; simp
    rw [this]; exact locallyIntegrableOn_zero
  · rw [quasiDeriv_zero L x hx, quasiDeriv_zero L y hy]
    simp

/-- The right-hand side of `τ f = F` is unique almost everywhere. -/
theorem tau_unique (L : SLData) {f G1 G2 : ℝ → ℂ} (h1 : SolvesTau L f G1)
    (h2 : SolvesTau L f G2) : G1 =ᵐ[L.measure] G2 := by
  refine ae_of_ae_vol L (ae_I_of_local L (fun s t hs ht hst => ?_))
  obtain ⟨-, l1, p1⟩ := h1
  obtain ⟨-, l2, p2⟩ := h2
  set k : ℝ → ℂ := fun u => ((L.q u : ℂ) * f u - (L.r u : ℂ) * G2 u) -
    ((L.q u : ℂ) * f u - (L.r u : ℂ) * G1 u)
  have hk : IntervalIntegrable k volume s t := (ii_of_loc L l2 hs ht).sub (ii_of_loc L l1 hs ht)
  have h0 : ∀ x ∈ Icc s t, ∫ u in s..x, k u = 0 := by
    intro x hx
    have hxI := Icc_sub_I L hs ht hx
    rw [intervalIntegral.integral_sub (ii_of_loc L l2 hs hxI) (ii_of_loc L l1 hs hxI),
      ← p1 s hs x hxI, ← p2 s hs x hxI, sub_self]
  filter_upwards [ae_zero_local hk h0, ae_restrict_mem measurableSet_Ioo] with u hu hmem
  have huI : u ∈ L.I := Icc_sub_I L hs ht (Ioo_subset_Icc_self hmem)
  have : (L.r u : ℂ) * (G1 u - G2 u) = 0 := by
    simp only [k] at hu; linear_combination hu
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (r_ne L huI)
  · exact sub_eq_zero.mp h

/-! ### The operator with graph `operatorGraph L D` -/

theorem solvesTau_add (L : SLData) {f1 f2 G1 G2 : ℝ → ℂ} (h1 : SolvesTau L f1 G1)
    (h2 : SolvesTau L f2 G2) : SolvesTau L (fun x => f1 x + f2 x) (fun x => G1 x + G2 x) := by
  have := (WeylLP.solvesTau_lin L h1 h2 1 1).1
  simp only [one_mul] at this
  exact this

theorem solvesTau_smul (L : SLData) {f G : ℝ → ℂ} (h : SolvesTau L f G) (a : ℂ) :
    SolvesTau L (fun x => a * f x) (fun x => a * G x) := by
  have := (WeylLP.solvesTau_lin L h h a 0).1
  simp only [zero_mul, add_zero] at this
  exact this

theorem qd_add (L : SLData) {f1 f2 G1 G2 : ℝ → ℂ} (h1 : SolvesTau L f1 G1)
    (h2 : SolvesTau L f2 G2) :
    ∀ x ∈ L.I, quasiDeriv L (fun x => f1 x + f2 x) x = quasiDeriv L f1 x + quasiDeriv L f2 x := by
  intro x hx
  have := (WeylLP.solvesTau_lin L h1 h2 1 1).2 x hx
  simp only [one_mul] at this
  exact this

theorem qd_smul (L : SLData) {f G : ℝ → ℂ} (h : SolvesTau L f G) (a : ℂ) :
    ∀ x ∈ L.I, quasiDeriv L (fun x => a * f x) x = a * quasiDeriv L f x := by
  intro x hx
  have := (WeylLP.solvesTau_lin L h h a 0).2 x hx
  simp only [zero_mul, add_zero] at this
  exact this

theorem exists_pmap (L : SLData) (D : (ℝ → ℂ) → Prop) (h0 : D 0)
    (hadd : ∀ f g, D f → D g → D (fun x => f x + g x))
    (hsmul : ∀ (a : ℂ) f, D f → D (fun x => a * f x)) :
    ∃ A : Lp ℂ 2 L.measure →ₗ.[ℂ] Lp ℂ 2 L.measure,
      (A.graph : Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure)) = operatorGraph L D := by
  let G : Submodule ℂ (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure) :=
    { carrier := operatorGraph L D
      zero_mem' := by
        refine ⟨0, 0, MemLp.zero, MemLp.zero, h0, solvesTau_zero L, ?_⟩
        simp only [MemLp.toLp_zero, Prod.mk_zero_zero]
      add_mem' := by
        rintro x y ⟨f1, g1, hf1, hg1, hD1, hs1, rfl⟩ ⟨f2, g2, hf2, hg2, hD2, hs2, rfl⟩
        refine ⟨fun x => f1 x + f2 x, fun x => g1 x + g2 x, hf1.add hf2, hg1.add hg2,
          hadd _ _ hD1 hD2, solvesTau_add L hs1 hs2, ?_⟩
        simp only [Prod.mk_add_mk]
        rw [← MemLp.toLp_add, ← MemLp.toLp_add]
        rfl
      smul_mem' := by
        rintro a x ⟨f, g, hf, hg, hD, hs, rfl⟩
        refine ⟨fun x => a * f x, fun x => a * g x, hf.const_smul a, hg.const_smul a,
          hsmul a _ hD, solvesTau_smul L hs a, ?_⟩
        simp only [Prod.smul_mk]
        rw [← MemLp.toLp_const_smul, ← MemLp.toLp_const_smul]
        rfl }
  refine ⟨G.toLinearPMap, ?_⟩
  rw [Submodule.toLinearPMap_graph_eq]
  · rfl
  · rintro x ⟨f, g, hf, hg, hD, hs, rfl⟩ hx0
    simp only at hx0 ⊢
    rw [Lp.eq_zero_iff_ae_eq_zero] at hx0 ⊢
    have hf0 : f =ᵐ[L.measure] 0 := (hf.coeFn_toLp.symm).trans hx0
    have hfI := eqOn_of_ae L (tau_contOn L hs) continuousOn_const hf0
    have hs0 : SolvesTau L (0 : ℝ → ℂ) g := solvesTau_congr L hfI hs
    have hg0 : g =ᵐ[L.measure] 0 := tau_unique L hs0 (solvesTau_zero L)
    exact hg.coeFn_toLp.trans hg0

/-! ### Linear structure of the domains -/

theorem inMax_zero (L : SLData) : InMaxDomain L 0 := ⟨MemLp.zero, 0, solvesTau_zero L, MemLp.zero⟩

theorem inMax_add (L : SLData) {f g : ℝ → ℂ} (hf : InMaxDomain L f) (hg : InMaxDomain L g) :
    InMaxDomain L (fun x => f x + g x) := by
  obtain ⟨hf2, F, hF, hF2⟩ := hf
  obtain ⟨hg2, G, hG, hG2⟩ := hg
  exact ⟨hf2.add hg2, _, solvesTau_add L hF hG, hF2.add hG2⟩

theorem inMax_smul (L : SLData) {f : ℝ → ℂ} (hf : InMaxDomain L f) (a : ℂ) :
    InMaxDomain L (fun x => a * f x) := by
  obtain ⟨hf2, F, hF, hF2⟩ := hf
  exact ⟨hf2.const_smul a, _, solvesTau_smul L hF a, hF2.const_smul a⟩

theorem wronskian_add_right (L : SLData) {v f g : ℝ → ℂ} (hf : InMaxDomain L f)
    (hg : InMaxDomain L g) {x : ℝ} (hx : x ∈ L.I) :
    wronskian L x v (fun x => f x + g x) = wronskian L x v f + wronskian L x v g := by
  obtain ⟨-, F, hF, -⟩ := hf
  obtain ⟨-, G, hG, -⟩ := hg
  unfold wronskian
  rw [qd_add L hF hG x hx]; ring

theorem wronskian_smul_right (L : SLData) {v f : ℝ → ℂ} (hf : InMaxDomain L f) (a : ℂ) {x : ℝ}
    (hx : x ∈ L.I) : wronskian L x v (fun x => a * f x) = a * wronskian L x v f := by
  obtain ⟨-, F, hF, -⟩ := hf
  unfold wronskian
  rw [qd_smul L hF a x hx]; ring

theorem wronskian_zero_right (L : SLData) {v : ℝ → ℂ} {x : ℝ} (hx : x ∈ L.I) :
    wronskian L x v 0 = 0 := by
  unfold wronskian
  rw [quasiDeriv_zero L x hx]; simp

theorem tendsto_W_right (L : SLData) {f g : ℝ → ℂ} (hf : InMaxDomain L f)
    (hg : InMaxDomain L g) :
    Tendsto (fun x => wronskian L x g f) L.atRight (𝓝 (wronskianRight L g f)) := by
  obtain ⟨hgc2, G, hG, hG2⟩ := BcAux.maxDomain_conj L hg
  obtain ⟨hf2, F, hF, hF2⟩ := hf
  have := (lagrange_identity_aux L f (fun x => starRingEnd ℂ (g x)) F G hf2 hgc2 hF hG hF2
    hG2).2.1
  rw [BcAux.conj_conj_fun] at this
  exact this

theorem wLeft_add (L : SLData) {v f g : ℝ → ℂ} (hv : InMaxDomain L v) (hf : InMaxDomain L f)
    (hg : InMaxDomain L g) :
    wronskianLeft L v (fun x => f x + g x) = wronskianLeft L v f + wronskianLeft L v g := by
  refine tendsto_nhds_unique (BcAux.tendsto_W L (inMax_add L hf hg) hv)
    (((BcAux.tendsto_W L hf hv).add (BcAux.tendsto_W L hg hv)).congr' ?_)
  filter_upwards [eventually_mem_left L] with x hx
  exact (wronskian_add_right L hf hg hx).symm

theorem wLeft_smul (L : SLData) {v f : ℝ → ℂ} (hv : InMaxDomain L v) (hf : InMaxDomain L f)
    (a : ℂ) : wronskianLeft L v (fun x => a * f x) = a * wronskianLeft L v f := by
  refine tendsto_nhds_unique (BcAux.tendsto_W L (inMax_smul L hf a) hv)
    (((BcAux.tendsto_W L hf hv).const_mul a).congr' ?_)
  filter_upwards [eventually_mem_left L] with x hx
  exact (wronskian_smul_right L hf a hx).symm

theorem wRight_add (L : SLData) {v f g : ℝ → ℂ} (hv : InMaxDomain L v) (hf : InMaxDomain L f)
    (hg : InMaxDomain L g) :
    wronskianRight L v (fun x => f x + g x) = wronskianRight L v f + wronskianRight L v g := by
  refine tendsto_nhds_unique (tendsto_W_right L (inMax_add L hf hg) hv)
    (((tendsto_W_right L hf hv).add (tendsto_W_right L hg hv)).congr' ?_)
  filter_upwards [eventually_mem_right L] with x hx
  exact (wronskian_add_right L hf hg hx).symm

theorem wRight_smul (L : SLData) {v f : ℝ → ℂ} (hv : InMaxDomain L v) (hf : InMaxDomain L f)
    (a : ℂ) : wronskianRight L v (fun x => a * f x) = a * wronskianRight L v f := by
  refine tendsto_nhds_unique (tendsto_W_right L (inMax_smul L hf a) hv)
    (((tendsto_W_right L hf hv).const_mul a).congr' ?_)
  filter_upwards [eventually_mem_right L] with x hx
  exact (wronskian_smul_right L hf a hx).symm

theorem wLeft_zero (L : SLData) {v : ℝ → ℂ} : wronskianLeft L v 0 = 0 :=
  wronskianLeft_of_eventually L ((eventually_mem_left L).mono fun _ hx => wronskian_zero_right L hx)

theorem wRight_zero (L : SLData) {v : ℝ → ℂ} : wronskianRight L v 0 = 0 :=
  wronskianRight_of_eventually L
    ((eventually_mem_right L).mono fun _ hx => wronskian_zero_right L hx)

/-- Hypotheses of Theorem 9.6 on the boundary functions. -/
def BcHyp (L : SLData) (v w : ℝ → ℂ) : Prop :=
  (IsLimitCircleLeft L → InMaxDomain L v ∧
      wronskianLeft L (fun x => starRingEnd ℂ (v x)) v = 0 ∧
      ∃ f : ℝ → ℂ, InMaxDomain L f ∧ wronskianLeft L v f ≠ 0) ∧
    (IsLimitCircleRight L → InMaxDomain L w ∧
      wronskianRight L (fun x => starRingEnd ℂ (w x)) w = 0 ∧
      ∃ f : ℝ → ℂ, InMaxDomain L f ∧ wronskianRight L w f ≠ 0)

theorem bc_zero (L : SLData) (v w : ℝ → ℂ) : bcDomain L v w 0 :=
  ⟨inMax_zero L, fun _ => wLeft_zero L, fun _ => wRight_zero L⟩

theorem bc_add (L : SLData) {v w : ℝ → ℂ} (H : BcHyp L v w) (f g : ℝ → ℂ)
    (hf : bcDomain L v w f) (hg : bcDomain L v w g) : bcDomain L v w (fun x => f x + g x) := by
  refine ⟨inMax_add L hf.1 hg.1, fun hl => ?_, fun hr => ?_⟩
  · rw [wLeft_add L (H.1 hl).1 hf.1 hg.1, hf.2.1 hl, hg.2.1 hl, add_zero]
  · rw [wRight_add L (H.2 hr).1 hf.1 hg.1, hf.2.2 hr, hg.2.2 hr, add_zero]

theorem bc_smul (L : SLData) {v w : ℝ → ℂ} (H : BcHyp L v w) (a : ℂ) (f : ℝ → ℂ)
    (hf : bcDomain L v w f) : bcDomain L v w (fun x => a * f x) := by
  refine ⟨inMax_smul L hf.1 a, fun hl => ?_, fun hr => ?_⟩
  · rw [wLeft_smul L (H.1 hl).1 hf.1, hf.2.1 hl, mul_zero]
  · rw [wRight_smul L (H.2 hr).1 hf.1, hf.2.2 hr, mul_zero]

theorem core_zero (L : SLData) (v w : ℝ → ℂ) : coreDomain L v w 0 := by
  obtain ⟨c, hc⟩ := exists_mem_I L
  exact ⟨inMax_zero L, fun _ => ⟨c, hc, fun x hx _ => wronskian_zero_right L hx⟩,
    fun _ => ⟨c, hc, fun x hx _ => wronskian_zero_right L hx⟩⟩

theorem core_add (L : SLData) {v w : ℝ → ℂ} (f g : ℝ → ℂ)
    (hf : coreDomain L v w f) (hg : coreDomain L v w g) :
    coreDomain L v w (fun x => f x + g x) := by
  refine ⟨inMax_add L hf.1 hg.1, fun hl => ?_, fun hr => ?_⟩
  · obtain ⟨x1, hx1, h1⟩ := hf.2.1 hl
    obtain ⟨x2, hx2, h2⟩ := hg.2.1 hl
    refine ⟨min x1 x2, by rcases min_choice x1 x2 with h | h <;> rw [h] <;> assumption,
      fun x hx hlt => ?_⟩
    rw [wronskian_add_right L hf.1 hg.1 hx, h1 x hx (hlt.trans_le (min_le_left _ _)),
      h2 x hx (hlt.trans_le (min_le_right _ _)), add_zero]
  · obtain ⟨x1, hx1, h1⟩ := hf.2.2 hr
    obtain ⟨x2, hx2, h2⟩ := hg.2.2 hr
    refine ⟨max x1 x2, by rcases max_choice x1 x2 with h | h <;> rw [h] <;> assumption,
      fun x hx hlt => ?_⟩
    rw [wronskian_add_right L hf.1 hg.1 hx, h1 x hx ((le_max_left _ _).trans_lt hlt),
      h2 x hx ((le_max_right _ _).trans_lt hlt), add_zero]

theorem core_smul (L : SLData) {v w : ℝ → ℂ} (a : ℂ) (f : ℝ → ℂ)
    (hf : coreDomain L v w f) : coreDomain L v w (fun x => a * f x) := by
  refine ⟨inMax_smul L hf.1 a, fun hl => ?_, fun hr => ?_⟩
  · obtain ⟨x1, hx1, h1⟩ := hf.2.1 hl
    exact ⟨x1, hx1, fun x hx hlt => by rw [wronskian_smul_right L hf.1 a hx, h1 x hx hlt,
      mul_zero]⟩
  · obtain ⟨x1, hx1, h1⟩ := hf.2.2 hr
    exact ⟨x1, hx1, fun x hx hlt => by rw [wronskian_smul_right L hf.1 a hx, h1 x hx hlt,
      mul_zero]⟩

theorem core_bc (L : SLData) {v w f : ℝ → ℂ} (hf : coreDomain L v w f) : bcDomain L v w f := by
  refine ⟨hf.1, fun hl => ?_, fun hr => ?_⟩
  · obtain ⟨x1, hx1, h1⟩ := hf.2.1 hl
    exact wronskianLeft_of_eventually L (((eventually_mem_left L).and
      (eventually_lt_left L hx1.1)).mono fun x hx => h1 x hx.1 hx.2)
  · obtain ⟨x1, hx1, h1⟩ := hf.2.2 hr
    exact wronskianRight_of_eventually L (((eventually_mem_right L).and
      (eventually_gt_right L hx1.2)).mono fun x hx => h1 x hx.1 hx.2)

/-- Functions vanishing (with their quasi-derivatives) near both endpoints lie in `D₁`. -/
theorem compact_core (L : SLData) {v w f : ℝ → ℂ} (hf : InMaxDomain L f) {c d : ℝ}
    (hc : c ∈ L.I) (hd : d ∈ L.I)
    (hl : ∀ x ∈ L.I, x ≤ c → f x = 0 ∧ quasiDeriv L f x = 0)
    (hr : ∀ x ∈ L.I, d ≤ x → f x = 0 ∧ quasiDeriv L f x = 0) : coreDomain L v w f := by
  refine ⟨hf, fun _ => ⟨c, hc, fun x hx hlt => ?_⟩, fun _ => ⟨d, hd, fun x hx hlt => ?_⟩⟩
  · obtain ⟨e1, e2⟩ := hl x hx hlt.le
    unfold wronskian; rw [e1, e2]; ring
  · obtain ⟨e1, e2⟩ := hr x hx hlt.le
    unfold wronskian; rw [e1, e2]; ring

end SAAux

end SecSA1

section SecSA2

/-!
# Splicing solutions and cut-off functions
-/

open MeasureTheory Set Filter Topology
open scoped Interval

namespace SAAux

open TeschlQM.SturmLiouville VoCAux LagAux IvpAux WeylAux

theorem locInt_ite (L : SLData) {h1 h2 : ℝ → ℂ} (c : ℝ) (l1 : LocallyIntegrableOn h1 L.I)
    (l2 : LocallyIntegrableOn h2 L.I) :
    LocallyIntegrableOn (fun t => if t ≤ c then h1 t else h2 t) L.I := by
  have e : (fun t => if t ≤ c then h1 t else h2 t) =
      fun t => (Iic c).indicator h1 t + (Ioi c).indicator h2 t := by
    funext t
    by_cases ht : t ≤ c
    · have : t ∉ Ioi c := fun h => absurd h (not_lt.mpr ht)
      simp [ht, this]
    · have : t ∈ Ioi c := not_le.mp ht
      simp [ht, this]
  rw [e]
  rw [locallyIntegrableOn_iff (I_lc L)] at l1 l2 ⊢
  intro k hk hkc
  exact ((l1 k hk hkc).indicator measurableSet_Iic).add ((l2 k hk hkc).indicator measurableSet_Ioi)

/-- Splicing of primitives at a point. -/
theorem prim_splice (L : SLData) {φ1 φ2 h1 h2 : ℝ → ℂ} {c : ℝ} (hc : c ∈ L.I)
    (l1 : LocallyIntegrableOn h1 L.I) (l2 : LocallyIntegrableOn h2 L.I)
    (p1 : ∀ x ∈ L.I, ∀ y ∈ L.I, φ1 y - φ1 x = ∫ t in x..y, h1 t)
    (p2 : ∀ x ∈ L.I, ∀ y ∈ L.I, φ2 y - φ2 x = ∫ t in x..y, h2 t) (e : φ1 c = φ2 c) :
    ∀ x ∈ L.I, ∀ y ∈ L.I, (if y ≤ c then φ1 y else φ2 y) - (if x ≤ c then φ1 x else φ2 x) =
      ∫ t in x..y, (if t ≤ c then h1 t else h2 t) := by
  set h : ℝ → ℂ := fun t => if t ≤ c then h1 t else h2 t
  have hl : LocallyIntegrableOn h L.I := locInt_ite L c l1 l2
  have key : ∀ x ∈ L.I, (if x ≤ c then φ1 x else φ2 x) = φ1 c + ∫ t in c..x, h t := by
    intro x hx
    by_cases hxc : x ≤ c
    · rw [if_pos hxc]
      have : ∫ t in c..x, h t = ∫ t in c..x, h1 t := by
        refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
        rw [uIoc_of_ge hxc] at ht
        simp only [h, if_pos ht.2]
      rw [this, ← p1 c hc x hx]; ring
    · rw [if_neg hxc]
      have : ∫ t in c..x, h t = ∫ t in c..x, h2 t := by
        refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
        rw [uIoc_of_le (not_le.mp hxc).le] at ht
        simp only [h, if_neg (not_le.mpr ht.1)]
      rw [this, ← p2 c hc x hx, e]; ring
  intro x hx y hy
  rw [key x hx, key y hy, ← intervalIntegral.integral_interval_sub_left (ii_of_loc L hl hc hy)
    (ii_of_loc L hl hc hx)]
  ring

/-- Splicing two solutions of `τ f = F` with matching data at `c`. -/
theorem splice (L : SLData) {f1 f2 F1 F2 : ℝ → ℂ} (h1 : SolvesTau L f1 F1)
    (h2 : SolvesTau L f2 F2) {c : ℝ} (hc : c ∈ L.I) (e0 : f1 c = f2 c)
    (e1 : quasiDeriv L f1 c = quasiDeriv L f2 c) :
    SolvesTau L (fun x => if x ≤ c then f1 x else f2 x) (fun x => if x ≤ c then F1 x else F2 x) ∧
      ∀ x ∈ L.I, quasiDeriv L (fun x => if x ≤ c then f1 x else f2 x) x =
        if x ≤ c then quasiDeriv L f1 x else quasiDeriv L f2 x := by
  obtain ⟨⟨⟨k1, hk1, hp1⟩, hl1, hq1⟩, hm1, hr1⟩ := h1
  obtain ⟨⟨⟨k2, hk2, hp2⟩, hl2, hq2⟩, hm2, hr2⟩ := h2
  set Q : ℝ → ℂ := fun x => if x ≤ c then quasiDeriv L f1 x else quasiDeriv L f2 x
  have hQp : (fun t => Q t / (L.p t : ℂ)) = fun t => if t ≤ c then quasiDeriv L f1 t /
      (L.p t : ℂ) else quasiDeriv L f2 t / (L.p t : ℂ) := by
    funext t; simp only [Q]; split_ifs <;> rfl
  have hQD : IsQuasiDerivative L (fun x => if x ≤ c then f1 x else f2 x) Q := by
    refine ⟨⟨fun t => if t ≤ c then k1 t else k2 t, locInt_ite L c hk1 hk2,
      prim_splice L hc hk1 hk2 hp1 hp2 e1⟩, ?_, ?_⟩
    · rw [hQp]; exact locInt_ite L c hl1 hl2
    · rw [hQp]; exact prim_splice L hc hl1 hl2 hq1 hq2 e0
  have hU := qd_unique L (isQD_quasiDeriv L hQD) hQD
  have hR : (fun t => (L.q t : ℂ) * (if t ≤ c then f1 t else f2 t) -
      (L.r t : ℂ) * (if t ≤ c then F1 t else F2 t)) = fun t => if t ≤ c then
        (L.q t : ℂ) * f1 t - (L.r t : ℂ) * F1 t else (L.q t : ℂ) * f2 t - (L.r t : ℂ) * F2 t := by
    funext t; split_ifs <;> rfl
  refine ⟨⟨isQD_quasiDeriv L hQD, ?_, fun x hx y hy => ?_⟩, hU⟩
  · rw [hR]; exact locInt_ite L c hm1 hm2
  · rw [hU x hx, hU y hy, hR]
    exact prim_splice L hc hm1 hm2 hr1 hr2 e1 x hx y hy

theorem memLp_Ioc (L : SLData) {V : ℝ → ℂ} (hV : ContinuousOn V L.I) {c d : ℝ} (hc : c ∈ L.I)
    (hd : d ∈ L.I) (hcd : c ≤ d) : MemLp ((Ioc c d).indicator V) 2 L.measure := by
  rw [memLp_indicator_iff_restrict measurableSet_Ioc,
    measure_restrict_eq L measurableSet_Ioc (Ioc_subset_Icc_self.trans (Icc_sub_I L hc hd))]
  exact memLp_mono_set L measurableSet_Ioc Ioc_subset_Icc_self (memLp_of_contOn L hc hd hcd hV)

theorem data_match (L : SLData) {u1 u2 : ℝ → ℂ} {c : ℝ}
    (hW : wronskian L c u1 u2 = 1) (A B : ℂ) :
    (A * quasiDeriv L u2 c - B * u2 c) * u1 c + (B * u1 c - A * quasiDeriv L u1 c) * u2 c = A ∧
    (A * quasiDeriv L u2 c - B * u2 c) * quasiDeriv L u1 c +
      (B * u1 c - A * quasiDeriv L u1 c) * quasiDeriv L u2 c = B := by
  unfold wronskian at hW
  constructor
  · linear_combination A * hW
  · linear_combination B * hW

/-- A cut-off of an element of `D(τ)`: equal to `v` left of `c`, zero right of some `d > c`. -/
theorem cutoff_left (L : SLData) {v V : ℝ → ℂ} (hv : SolvesTau L v V) (hv2 : MemLp v 2 L.measure)
    (hV2 : MemLp V 2 L.measure) {c : ℝ} (hc : c ∈ L.I) :
    ∃ f F : ℝ → ℂ, ∃ d ∈ L.I, c < d ∧ SolvesTau L f F ∧ MemLp f 2 L.measure ∧
      MemLp F 2 L.measure ∧
      (∀ x ∈ L.I, x ≤ c → f x = v x ∧ quasiDeriv L f x = quasiDeriv L v x) ∧
      (∀ x ∈ L.I, d ≤ x → f x = 0 ∧ quasiDeriv L f x = 0) := by
  obtain ⟨u1, u2, h1, h2, hW⟩ := fund_system L 0
  obtain ⟨-, d, -, hcd, -, hd⟩ := exists_Icc_subset_I L hc
  set α0 := v c * quasiDeriv L u2 c - quasiDeriv L v c * u2 c
  set β0 := quasiDeriv L v c * u1 c - v c * quasiDeriv L u1 c
  obtain ⟨m1, m2⟩ := data_match L (hW c hc) (v c) (quasiDeriv L v c)
  obtain ⟨φ, V2, hφ, hV2s, hl, hr⟩ := glue L 0 h1 h2 hW hc hd hcd α0 β0 β0 (-α0)
  have hV2c := sol_contOn L hV2s
  have e0 : v c = V2 c := by rw [(hl c hc le_rfl).1]; exact m1.symm
  have e1 : quasiDeriv L v c = quasiDeriv L V2 c := by rw [(hl c hc le_rfl).2]; exact m2.symm
  obtain ⟨hs, hq⟩ := splice L hv hV2s hc e0 e1
  have hzero : ∀ x ∈ L.I, d ≤ x → V2 x = 0 ∧ quasiDeriv L V2 x = 0 := by
    intro x hx hdx
    obtain ⟨a1, a2⟩ := hr x hx hdx
    constructor
    · rw [a1]; ring
    · rw [a2]; ring
  refine ⟨_, _, d, hd, hcd, hs, ?_, ?_, fun x hx hxc => ?_, fun x hx hdx => ?_⟩
  · refine ((MemLp.indicator (s := Iic c) measurableSet_Iic hv2).add
      (memLp_Ioc L hV2c hc hd hcd.le)).ae_eq (ae_measure_of_forall L (fun x hx => ?_))
    by_cases hxc : x ≤ c
    · have h2 : ¬ (c < x ∧ x ≤ d) := fun h => absurd h.1 (not_lt.mpr hxc)
      simp [hxc, h2]
    · by_cases hxd : x ≤ d
      · have h2 : c < x ∧ x ≤ d := ⟨not_le.mp hxc, hxd⟩
        simp [hxc, h2]
      · have h2 : ¬ (c < x ∧ x ≤ d) := fun h => hxd h.2
        simp [hxc, h2, (hzero x hx (not_le.mp hxd).le).1]
  · refine ((MemLp.indicator (s := Iic c) measurableSet_Iic hV2).add
      (memLp_Ioc L hφ hc hd hcd.le)).ae_eq (ae_measure_of_forall L (fun x hx => ?_))
    by_cases hxc : x ≤ c
    · have h2 : ¬ (c < x ∧ x ≤ d) := fun h => absurd h.1 (not_lt.mpr hxc)
      simp [hxc, h2]
    · by_cases hxd : x ≤ d
      · have h2 : c < x ∧ x ≤ d := ⟨not_le.mp hxc, hxd⟩
        simp [hxc, h2]
      · have h2 : ¬ (c < x ∧ x ≤ d) := fun h => hxd h.2
        simp [hxc, h2]
  · rw [hq x hx]; simp [hxc]
  · have hxc : ¬ x ≤ c := fun h => absurd (h.trans_lt hcd) (not_lt.mpr hdx)
    rw [hq x hx]; simp only [if_neg hxc]; exact hzero x hx hdx

/-- A cut-off of an element of `D(τ)`: equal to `w` right of `c`, zero left of some `d < c`. -/
theorem cutoff_right (L : SLData) {v V : ℝ → ℂ} (hv : SolvesTau L v V)
    (hv2 : MemLp v 2 L.measure) (hV2 : MemLp V 2 L.measure) {c : ℝ} (hc : c ∈ L.I) :
    ∃ f F : ℝ → ℂ, ∃ d ∈ L.I, d < c ∧ SolvesTau L f F ∧ MemLp f 2 L.measure ∧
      MemLp F 2 L.measure ∧
      (∀ x ∈ L.I, c ≤ x → f x = v x ∧ quasiDeriv L f x = quasiDeriv L v x) ∧
      (∀ x ∈ L.I, x ≤ d → f x = 0 ∧ quasiDeriv L f x = 0) := by
  obtain ⟨u1, u2, h1, h2, hW⟩ := fund_system L 0
  obtain ⟨d, -, hdc, -, hd, -⟩ := exists_Icc_subset_I L hc
  set α0 := v c * quasiDeriv L u2 c - quasiDeriv L v c * u2 c
  set β0 := quasiDeriv L v c * u1 c - v c * quasiDeriv L u1 c
  obtain ⟨m1, m2⟩ := data_match L (hW c hc) (v c) (quasiDeriv L v c)
  obtain ⟨φ, V2, hφ, hV2s, hl, hr⟩ := glue L 0 h1 h2 hW hd hc hdc 0 0 (-β0) α0
  have hV2c := sol_contOn L hV2s
  have e0 : V2 c = v c := by
    rw [(hr c hc le_rfl).1, ← m1]; ring
  have e1 : quasiDeriv L V2 c = quasiDeriv L v c := by
    rw [(hr c hc le_rfl).2, ← m2]; ring
  obtain ⟨hs, hq⟩ := splice L hV2s hv hc e0 e1
  have hzero : ∀ x ∈ L.I, x ≤ d → V2 x = 0 ∧ quasiDeriv L V2 x = 0 := by
    intro x hx hxd
    obtain ⟨a1, a2⟩ := hl x hx hxd
    constructor
    · rw [a1]; ring
    · rw [a2]; ring
  refine ⟨_, _, d, hd, hdc, hs, ?_, ?_, fun x hx hcx => ?_, fun x hx hxd => ?_⟩
  · refine ((memLp_Ioc L hV2c hd hc hdc.le).add (MemLp.indicator (s := Ioi c) measurableSet_Ioi
      hv2)).ae_eq (ae_measure_of_forall L (fun x hx => ?_))
    by_cases hxc : x ≤ c
    · have h3 : ¬ c < x := not_lt.mpr hxc
      by_cases hxd : d < x
      · have h2 : d < x ∧ x ≤ c := ⟨hxd, hxc⟩
        simp [hxc, h2, h3]
      · have h2 : ¬ (d < x ∧ x ≤ c) := fun h => hxd h.1
        simp [hxc, h3, (hzero x hx (not_lt.mp hxd)).1]
    · have h2 : ¬ (d < x ∧ x ≤ c) := fun h => hxc h.2
      simp [hxc, not_le.mp hxc]
  · refine ((memLp_Ioc L hφ hd hc hdc.le).add (MemLp.indicator (s := Ioi c) measurableSet_Ioi
      hV2)).ae_eq (ae_measure_of_forall L (fun x hx => ?_))
    by_cases hxc : x ≤ c
    · have h3 : ¬ c < x := not_lt.mpr hxc
      by_cases hxd : d < x
      · have h2 : d < x ∧ x ≤ c := ⟨hxd, hxc⟩
        simp [hxc, h2, h3]
      · have h2 : ¬ (d < x ∧ x ≤ c) := fun h => hxd h.1
        simp [hxc, h3]
    · have h2 : ¬ (d < x ∧ x ≤ c) := fun h => hxc h.2
      simp [hxc, not_le.mp hxc]
  · rw [hq x hx]
    by_cases hxc : x ≤ c
    · have hxe : x = c := le_antisymm hxc hcx
      subst hxe
      simp only [if_pos hxc]; exact ⟨e0, e1⟩
    · simp [hxc]
  · have hxc : x ≤ c := hxd.trans hdc.le
    rw [hq x hx]; simp only [if_pos hxc]; exact hzero x hx hxd

end SAAux

end SecSA2

section SecSA3

/-!
# Local regularity: weak solutions of `τ w = k` are strong solutions

If `⟨w, τ f⟩ = ⟨k, f⟩` for all compactly supported `f ∈ D(τ)`, then `w` agrees almost everywhere
with an element of `D(τ)` solving `τ w = k`.
-/

open MeasureTheory Set Filter Topology
open scoped Interval

namespace SAAux

open TeschlQM.SturmLiouville VoCAux LagAux IvpAux WeylAux

/-- `r k` is locally integrable for `k ∈ L²(r dx)`. -/
theorem rk_loc (L : SLData) {k : ℝ → ℂ} (hk : MemLp k 2 L.measure) :
    LocallyIntegrableOn (fun x => (L.r x : ℂ) * k x) L.I := by
  rw [locallyIntegrableOn_iff (I_lc L)]
  intro K hK hKc
  have hKm : MeasurableSet K := hKc.measurableSet
  have hr : IntegrableOn L.r K := L.r_loc.integrableOn_compact_subset hK hKc
  have h1 : MemLp k 2 (L.measure.restrict K) := hk.restrict K
  haveI : IsFiniteMeasure (L.measure.restrict K) := by
    rw [measure_restrict_eq L hKm hK]; exact isFiniteMeasure_withDensity_ofReal hr.2
  have h2 : Integrable (K.indicator k) L.measure :=
    (integrable_indicator_iff hKm).mpr (h1.integrable one_le_two)
  have h3 := (integrableOn_of_integrable_measure L h2).mono_set hK
  refine IntegrableOn.congr_fun h3 (fun x hx => ?_) hKm
  simp only [indicator_of_mem hx]

theorem intOn_rk (L : SLData) {k : ℝ → ℂ} (hk : MemLp k 2 L.measure) {c d : ℝ} (hc : c ∈ L.I)
    (hd : d ∈ L.I) : IntegrableOn (fun x => (L.r x : ℂ) * k x) (Icc c d) :=
  (rk_loc L hk).integrableOn_compact_subset (Icc_sub_I L hc hd) isCompact_Icc

theorem intOn_mul_cont (L : SLData) {ρ χ : ℝ → ℂ} {c d : ℝ} (hc : c ∈ L.I) (hd : d ∈ L.I)
    (hρ : IntegrableOn ρ (Icc c d)) (hχ : ContinuousOn χ L.I) :
    IntegrableOn (fun x => ρ x * χ x) (Ioc c d) :=
  (hρ.mono_set Ioc_subset_Icc_self).mul_continuousOn_of_subset (hχ.mono (Icc_sub_I L hc hd))
    measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self

/-- Solution of `τ f = 1_{(c,d]} χ` with zero data at `c`, and its tail right of `d`. -/
theorem ivp_compact (L : SLData) {u1 u2 : ℝ → ℂ} (h1 : IsSolution L 0 0 u1)
    (h2 : IsSolution L 0 0 u2) (hW : ∀ x ∈ L.I, wronskian L x u1 u2 = 1) {c d : ℝ}
    (hc : c ∈ L.I) (hd : d ∈ L.I) (hcd : c < d) {χ : ℝ → ℂ} (hχ : ContinuousOn χ L.I) :
    ∃ f : ℝ → ℂ, IsSolution L 0 ((Ioc c d).indicator χ) f ∧
      (∀ x ∈ L.I, x ≤ c → f x = 0 ∧ quasiDeriv L f x = 0) ∧
      (∀ x ∈ L.I, d ≤ x →
        f x = (∫ y in c..d, u2 y * (Ioc c d).indicator χ y * (L.r y : ℂ)) * u1 x -
          (∫ y in c..d, u1 y * (Ioc c d).indicator χ y * (L.r y : ℂ)) * u2 x ∧
        quasiDeriv L f x =
          (∫ y in c..d, u2 y * (Ioc c d).indicator χ y * (L.r y : ℂ)) * quasiDeriv L u1 x -
          (∫ y in c..d, u1 y * (Ioc c d).indicator χ y * (L.r y : ℂ)) * quasiDeriv L u2 x) := by
  have hu1 := sol_contOn L h1
  have hu2 := sol_contOn L h2
  set g := (Ioc c d).indicator χ with hgdef
  have hg : LocallyIntegrableOn (fun x => (L.r x : ℂ) * g x) L.I := by
    have e : (fun x => (L.r x : ℂ) * g x) = (Ioc c d).indicator (fun x => χ x * (L.r x : ℂ)) := by
      funext x
      by_cases hx : x ∈ Ioc c d
      · simp [hgdef, indicator_of_mem hx, mul_comm]
      · simp [hgdef, indicator_of_notMem hx]
    rw [e]
    exact ((integrable_indicator_iff measurableSet_Ioc).mpr
      (intOn_Ioc L hχ hc hd hcd.le)).locallyIntegrable.locallyIntegrableOn _
  obtain ⟨F, hF, -, -⟩ := IvpAux.ivp L g hg c hc 0 0
  obtain ⟨hv, hvc, hvqc⟩ := hF 0
  obtain ⟨α, β, hvoc⟩ := voc L 0 g u1 u2 h1 h2 hW c hc (F 0) hv
  have ec := hvoc c hc
  simp only [intervalIntegral.integral_same, add_zero, sub_zero] at ec
  have hWc := hW c hc
  unfold wronskian at hWc
  have E1 : α * u1 c + β * u2 c = 0 := by linear_combination -ec.1 + hvc
  have E2 : α * quasiDeriv L u1 c + β * quasiDeriv L u2 c = 0 := by
    linear_combination -ec.2 + hvqc
  have hα : α = 0 := by
    linear_combination quasiDeriv L u2 c * E1 - u2 c * E2 - α * hWc
  have hβ : β = 0 := by
    linear_combination u1 c * E2 - quasiDeriv L u1 c * E1 - β * hWc
  have hloc : ∀ {f : ℝ → ℂ}, ContinuousOn f L.I →
      LocallyIntegrableOn (fun y => f y * g y * (L.r y : ℂ)) L.I := by
    intro f hf
    have e : (fun y => f y * g y * (L.r y : ℂ)) = fun y => f y * ((L.r y : ℂ) * g y) := by
      funext y; ring
    rw [e]
    exact hg.continuousOn_mul hf (I_lc L)
  have htail : ∀ {f : ℝ → ℂ}, ContinuousOn f L.I → ∀ x ∈ L.I, d ≤ x →
      ∫ y in c..x, f y * g y * (L.r y : ℂ) = ∫ y in c..d, f y * g y * (L.r y : ℂ) := by
    intro f hf x hx hdx
    rw [← intervalIntegral.integral_add_adjacent_intervals (ii_of_loc L (hloc hf) hc hd)
      (ii_of_loc L (hloc hf) hd hx), int_tail_zero L hdx, add_zero]
  refine ⟨F 0, hv, fun x hx hxc => ?_, fun x hx hdx => ?_⟩
  · have e := hvoc x hx
    rw [int_zero_of_le L hxc, int_zero_of_le L hxc, hα, hβ] at e
    constructor
    · rw [e.1]; ring
    · rw [e.2]; ring
  · have e := hvoc x hx
    rw [htail hu1 x hx hdx, htail hu2 x hx hdx, hα, hβ] at e
    constructor
    · rw [e.1]; ring
    · rw [e.2]; ring

/-- Local Lagrange identity for a test function vanishing near `c` and `d`. -/
theorem local_lagrange (L : SLData) {k u f G : ℝ → ℂ} (hu : IsSolution L 0 k u)
    (hf : IsSolution L 0 G f) {c d : ℝ} (hc : c ∈ L.I) (hd : d ∈ L.I)
    (hfc : f c = 0 ∧ quasiDeriv L f c = 0) (hfd : f d = 0 ∧ quasiDeriv L f d = 0) :
    ∫ t in c..d, (L.r t : ℂ) * (starRingEnd ℂ (k t) * f t - starRingEnd ℂ (u t) * G t) = 0 := by
  have hd' := wronskian_diff L hf (solvesTau_conj L hu) hc hd
  have e1 : wronskian L d (fun x => starRingEnd ℂ (u x)) f = 0 := by
    unfold wronskian; rw [hfd.1, hfd.2]; ring
  have e2 : wronskian L c (fun x => starRingEnd ℂ (u x)) f = 0 := by
    unfold wronskian; rw [hfc.1, hfc.2]; ring
  rw [e1, e2, sub_zero] at hd'
  rw [hd']
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  simp

end SAAux

namespace SAAux

open TeschlQM.SturmLiouville VoCAux LagAux IvpAux WeylAux

/-- The weak-solution hypothesis of the local regularity lemma. -/
def WeakHyp (L : SLData) (w k : ℝ → ℂ) : Prop :=
  ∀ c d : ℝ, c ∈ L.I → d ∈ L.I → c < d → ∀ f F : ℝ → ℂ, SolvesTau L f F →
    MemLp f 2 L.measure → MemLp F 2 L.measure →
    (∀ x ∈ L.I, x ≤ c → f x = 0 ∧ quasiDeriv L f x = 0) →
    (∀ x ∈ L.I, d ≤ x → f x = 0 ∧ quasiDeriv L f x = 0) →
    ∫ x, starRingEnd ℂ (w x) * F x ∂L.measure = ∫ x, starRingEnd ℂ (k x) * f x ∂L.measure

theorem intOn_cont_r (L : SLData) {φ : ℝ → ℂ} (hφ : ContinuousOn φ L.I) {c d : ℝ}
    (hc : c ∈ L.I) (hd : d ∈ L.I) : IntegrableOn (fun x => (L.r x : ℂ) * φ x) (Icc c d) :=
  ((r_loc' L).integrableOn_compact_subset (Icc_sub_I L hc hd) isCompact_Icc).mul_continuousOn
    (hφ.mono (Icc_sub_I L hc hd)) isCompact_Icc

/-- Per-interval consequence of the weak equation. -/
theorem weak_interval (L : SLData) {w k u u1 u2 : ℝ → ℂ} (hw : MemLp w 2 L.measure)
    (hk : MemLp k 2 L.measure) (hu : IsSolution L 0 k u) (h1 : IsSolution L 0 0 u1)
    (h2 : IsSolution L 0 0 u2) (hW : ∀ x ∈ L.I, wronskian L x u1 u2 = 1) (H : WeakHyp L w k)
    {c d : ℝ} (hc : c ∈ L.I) (hd : d ∈ L.I) (hcd : c < d) {χ : ℝ → ℂ}
    (hχ : ContinuousOn χ L.I)
    (hP1 : ∫ y in c..d, u1 y * (Ioc c d).indicator χ y * (L.r y : ℂ) = 0)
    (hP2 : ∫ y in c..d, u2 y * (Ioc c d).indicator χ y * (L.r y : ℂ) = 0) :
    ∫ x in Ioc c d, starRingEnd ℂ (w x - u x) * χ x * (L.r x : ℂ) = 0 := by
  obtain ⟨f, hf, hl, hr⟩ := ivp_compact L h1 h2 hW hc hd hcd hχ
  set G := (Ioc c d).indicator χ with hG
  have hr' : ∀ x ∈ L.I, d ≤ x → f x = 0 ∧ quasiDeriv L f x = 0 := by
    intro x hx hdx
    obtain ⟨e1, e2⟩ := hr x hx hdx
    rw [hP1, hP2] at e1 e2
    exact ⟨by rw [e1]; ring, by rw [e2]; ring⟩
  have hfc : ContinuousOn f L.I := sol_contOn L hf
  have hout : ∀ x ∈ L.I, x ∉ Ioc c d → f x = 0 := by
    intro x hx hx'
    by_cases hxc : x ≤ c
    · exact (hl x hx hxc).1
    · exact (hr' x hx (by
        by_contra h; exact hx' ⟨not_le.mp hxc, (not_le.mp h).le⟩)).1
  have hf2 : MemLp f 2 L.measure := by
    refine (memLp_Ioc L hfc hc hd hcd.le).ae_eq (ae_measure_of_forall L (fun x hx => ?_))
    by_cases hx' : x ∈ Ioc c d
    · simp [indicator_of_mem hx']
    · simp [indicator_of_notMem hx', hout x hx hx']
  have hF2 : MemLp (fun x => 0 * f x + G x) 2 L.measure :=
    (memLp_Ioc L hχ hc hd hcd.le).ae_eq (Eventually.of_forall fun x => by simp [hG])
  have hH := H c d hc hd hcd f _ hf hf2 hF2 hl hr'
  have hIm := (I_isOpen L).measurableSet
  have hsub : Ioc c d ⊆ L.I := Ioc_subset_Icc_self.trans (Icc_sub_I L hc hd)
  rw [integral_measure_eq, integral_measure_eq,
    setIntegral_eq_of_subset_of_forall_diff_eq_zero hIm hsub (fun x hx => by
      simp [hG, indicator_of_notMem hx.2]),
    setIntegral_eq_of_subset_of_forall_diff_eq_zero hIm hsub (fun x hx => by
      simp [hout x hx.1 hx.2])] at hH
  have A1 : ∫ x in Ioc c d, (L.r x : ℂ) * starRingEnd ℂ (w x) * χ x =
      ∫ x in Ioc c d, (L.r x : ℂ) * starRingEnd ℂ (k x) * f x := by
    have e1 : ∫ x in Ioc c d, (L.r x : ℂ) * (starRingEnd ℂ (w x) * (0 * f x + G x)) =
        ∫ x in Ioc c d, (L.r x : ℂ) * starRingEnd ℂ (w x) * χ x :=
      setIntegral_congr_fun measurableSet_Ioc (fun x hx => by rw [hG, indicator_of_mem hx]; ring)
    have e2 : ∫ x in Ioc c d, (L.r x : ℂ) * (starRingEnd ℂ (k x) * f x) =
        ∫ x in Ioc c d, (L.r x : ℂ) * starRingEnd ℂ (k x) * f x :=
      setIntegral_congr_fun measurableSet_Ioc (fun x _ => by ring)
    rw [← e1, ← e2]; exact hH
  have I_kf : IntegrableOn (fun x => (L.r x : ℂ) * starRingEnd ℂ (k x) * f x) (Ioc c d) :=
    intOn_mul_cont L hc hd (intOn_rk L hk.star hc hd) hfc
  have I_u : IntegrableOn (fun x => (L.r x : ℂ) * starRingEnd ℂ (u x) * χ x) (Ioc c d) :=
    intOn_mul_cont L hc hd
    (intOn_cont_r L (Complex.continuous_conj.comp_continuousOn (sol_contOn L hu)) hc hd) hχ
  have I_w : IntegrableOn (fun x => (L.r x : ℂ) * starRingEnd ℂ (w x) * χ x) (Ioc c d) :=
    intOn_mul_cont L hc hd (intOn_rk L hw.star hc hd) hχ
  have hLag := local_lagrange L hu hf hc hd (hl c hc le_rfl) (hr' d hd le_rfl)
  rw [intervalIntegral.integral_of_le hcd.le] at hLag
  have A2 : ∫ x in Ioc c d, (L.r x : ℂ) * starRingEnd ℂ (k x) * f x =
      ∫ x in Ioc c d, (L.r x : ℂ) * starRingEnd ℂ (u x) * χ x := by
    rw [← sub_eq_zero, ← integral_sub I_kf I_u, ← hLag]
    refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
    rw [hG, indicator_of_mem hx]; ring
  rw [show (fun x => starRingEnd ℂ (w x - u x) * χ x * (L.r x : ℂ)) = fun x =>
      (L.r x : ℂ) * starRingEnd ℂ (w x) * χ x - (L.r x : ℂ) * starRingEnd ℂ (u x) * χ x by
    funext x; simp only [map_sub]; ring, integral_sub I_w I_u, A1, A2, sub_self]

end SAAux

namespace SAAux

open TeschlQM.SturmLiouville VoCAux LagAux IvpAux WeylAux

theorem P_conv (L : SLData) {f χ : ℝ → ℂ} {c d : ℝ} (hcd : c ≤ d) :
    ∫ y in c..d, f y * (Ioc c d).indicator χ y * (L.r y : ℂ) =
      ∫ y in Ioc c d, f y * χ y * (L.r y : ℂ) := by
  rw [intervalIntegral.integral_of_le hcd]
  exact setIntegral_congr_fun measurableSet_Ioc (fun y hy => by rw [indicator_of_mem hy])

/-- On each compact subinterval, `conj (w - u)` is a combination of the fundamental system. -/
theorem local_rep (L : SLData) {w k u u1 u2 : ℝ → ℂ} (hw : MemLp w 2 L.measure)
    (hk : MemLp k 2 L.measure) (hu : IsSolution L 0 k u) (h1 : IsSolution L 0 0 u1)
    (h2 : IsSolution L 0 0 u2) (hW : ∀ x ∈ L.I, wronskian L x u1 u2 = 1) (H : WeakHyp L w k)
    {c d : ℝ} (hc : c ∈ L.I) (hd : d ∈ L.I) (hcd : c < d) :
    ∃ A B : ℂ, ∀ᵐ x ∂(volume.restrict (Ioo c d)),
      starRingEnd ℂ (w x - u x) = A * u1 x + B * u2 x := by
  have hu1 := sol_contOn L h1
  have hu2 := sol_contOn L h2
  have hcu1 : ContinuousOn (fun x => starRingEnd ℂ (u1 x)) L.I :=
    Complex.continuous_conj.comp_continuousOn hu1
  have hcu2 : ContinuousOn (fun x => starRingEnd ℂ (u2 x)) L.I :=
    Complex.continuous_conj.comp_continuousOn hu2
  have hD := gram_ne L h1 h2 hW hc hd hcd
  set G11 := gram L c d u1 u1
  set G12 := gram L c d u1 u2
  set G21 := gram L c d u2 u1
  set G22 := gram L c d u2 u2
  set D := G11 * G22 - G12 * G21 with hDdef
  -- integrability of `conj (w - u) * φ * r`
  have hρ : IntegrableOn (fun x => starRingEnd ℂ (w x - u x) * (L.r x : ℂ)) (Icc c d) := by
    have := (intOn_rk L hw.star hc hd).sub
      (intOn_cont_r L (Complex.continuous_conj.comp_continuousOn (sol_contOn L hu)) hc hd)
    refine IntegrableOn.congr_fun this (fun x _ => ?_) measurableSet_Icc
    simp only [Pi.sub_apply, Function.comp_apply, map_sub, Pi.star_apply, Complex.star_def]; ring
  have I_m : ∀ {φ : ℝ → ℂ}, ContinuousOn φ L.I →
      IntegrableOn (fun x => starRingEnd ℂ (w x - u x) * φ x * (L.r x : ℂ)) (Ioc c d) := by
    intro φ hφ
    refine IntegrableOn.congr_fun (intOn_mul_cont L hc hd hρ hφ) (fun x _ => ?_)
      measurableSet_Ioc
    (try dsimp only); ring
  have I_c : ∀ {φ : ℝ → ℂ}, ContinuousOn φ L.I →
      IntegrableOn (fun x => φ x * (L.r x : ℂ)) (Ioc c d) :=
    fun hφ => intOn_Ioc L hφ hc hd hcd.le
  set ℓ1 := ∫ x in Ioc c d, starRingEnd ℂ (w x - u x) * starRingEnd ℂ (u1 x) * (L.r x : ℂ)
  set ℓ2 := ∫ x in Ioc c d, starRingEnd ℂ (w x - u x) * starRingEnd ℂ (u2 x) * (L.r x : ℂ)
  set A := (G22 * ℓ1 - G12 * ℓ2) / D
  set B := (G11 * ℓ2 - G21 * ℓ1) / D
  -- the key identity for every continuous real `g`
  have key : ∀ g : ℝ → ℝ, Continuous g →
      ∫ x in Ioc c d, (starRingEnd ℂ (w x - u x) - A * u1 x - B * u2 x) * (g x : ℂ) *
        (L.r x : ℂ) = 0 := by
    intro g hg
    obtain ⟨χ0, hχ0d⟩ : ∃ χ0 : ℝ → ℂ, χ0 = fun x => (g x : ℂ) := ⟨_, rfl⟩
    have hχ0 : ContinuousOn χ0 L.I := by
      rw [hχ0d]; exact (Complex.continuous_ofReal.comp hg).continuousOn
    obtain ⟨p1, hp1def⟩ : ∃ p : ℂ, p = ∫ x in Ioc c d, u1 x * χ0 x * (L.r x : ℂ) := ⟨_, rfl⟩
    obtain ⟨p2, hp2def⟩ : ∃ p : ℂ, p = ∫ x in Ioc c d, u2 x * χ0 x * (L.r x : ℂ) := ⟨_, rfl⟩
    obtain ⟨γ1, hγ1⟩ : ∃ γ : ℂ, γ = (p1 * G22 - p2 * G21) / D := ⟨_, rfl⟩
    obtain ⟨γ2, hγ2⟩ : ∃ γ : ℂ, γ = (p2 * G11 - p1 * G12) / D := ⟨_, rfl⟩
    obtain ⟨ψ, hψd⟩ : ∃ ψ : ℝ → ℂ, ψ = fun x => γ1 * starRingEnd ℂ (u1 x) +
      γ2 * starRingEnd ℂ (u2 x) := ⟨_, rfl⟩
    have hψ : ContinuousOn ψ L.I := by
      rw [hψd]; exact (continuousOn_const.mul hcu1).add (continuousOn_const.mul hcu2)
    -- `P_j(ψ) = γ1 G1j + γ2 G2j`
    have Pψ : ∀ {f : ℝ → ℂ}, ContinuousOn f L.I →
        ∫ x in Ioc c d, f x * ψ x * (L.r x : ℂ) =
          γ1 * gram L c d u1 f + γ2 * gram L c d u2 f := by
      intro f hf
      unfold gram
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add
        ((gram_int L hu1 hf hc hd hcd.le).const_mul γ1)
        ((gram_int L hu2 hf hc hd hcd.le).const_mul γ2)]
      refine setIntegral_congr_fun measurableSet_Ioc (fun x _ => ?_)
      simp only [hψd]; ring
    have hP : ∀ {f : ℝ → ℂ}, ContinuousOn f L.I →
        ∫ y in c..d, f y * (Ioc c d).indicator (fun x => χ0 x - ψ x) y * (L.r y : ℂ) =
          (∫ x in Ioc c d, f x * χ0 x * (L.r x : ℂ)) - (γ1 * gram L c d u1 f +
            γ2 * gram L c d u2 f) := by
      intro f hf
      have ia : IntegrableOn (fun x => f x * χ0 x * (L.r x : ℂ)) (Ioc c d) := I_c (hf.mul hχ0)
      have ib : IntegrableOn (fun x => f x * ψ x * (L.r x : ℂ)) (Ioc c d) := I_c (hf.mul hψ)
      rw [P_conv L hcd.le, ← Pψ hf]
      refine Eq.trans ?_ (integral_sub ia ib)
      exact setIntegral_congr_fun measurableSet_Ioc (fun x _ => by ring)
    have hP1 := hP hu1
    have hP2 := hP hu2
    have e1 : γ1 * G11 + γ2 * G21 = p1 := by
      rw [hγ1, hγ2]; field_simp; ring
    have e2 : γ1 * G12 + γ2 * G22 = p2 := by
      rw [hγ1, hγ2]; field_simp; ring
    have hP1' : ∫ y in c..d, u1 y * (Ioc c d).indicator (fun x => χ0 x - ψ x) y *
        (L.r y : ℂ) = 0 := by
      rw [hP1, show γ1 * gram L c d u1 u1 + γ2 * gram L c d u2 u1 = p1 from e1, hp1def, sub_self]
    have hP2' : ∫ y in c..d, u2 y * (Ioc c d).indicator (fun x => χ0 x - ψ x) y *
        (L.r y : ℂ) = 0 := by
      rw [hP2, show γ1 * gram L c d u1 u2 + γ2 * gram L c d u2 u2 = p2 from e2, hp2def, sub_self]
    have hwk := weak_interval L hw hk hu h1 h2 hW H hc hd hcd (hχ0.sub hψ) hP1' hP2'
    -- expand
    have E : ∫ x in Ioc c d, starRingEnd ℂ (w x - u x) * χ0 x * (L.r x : ℂ) =
        γ1 * ℓ1 + γ2 * ℓ2 := by
      have i1 := (I_m hcu1).const_mul γ1
      have i2 := (I_m hcu2).const_mul γ2
      have i12 : IntegrableOn (fun x =>
          γ1 * (starRingEnd ℂ (w x - u x) * starRingEnd ℂ (u1 x) * (L.r x : ℂ)) +
          γ2 * (starRingEnd ℂ (w x - u x) * starRingEnd ℂ (u2 x) * (L.r x : ℂ))) (Ioc c d) :=
        i1.add i2
      have : ∫ x in Ioc c d, starRingEnd ℂ (w x - u x) * (χ0 x - ψ x) * (L.r x : ℂ) =
          (∫ x in Ioc c d, starRingEnd ℂ (w x - u x) * χ0 x * (L.r x : ℂ)) -
            (γ1 * ℓ1 + γ2 * ℓ2) := by
        have e : ∫ x in Ioc c d, starRingEnd ℂ (w x - u x) * (χ0 x - ψ x) * (L.r x : ℂ) =
            ∫ x in Ioc c d, (starRingEnd ℂ (w x - u x) * χ0 x * (L.r x : ℂ) -
              (γ1 * (starRingEnd ℂ (w x - u x) * starRingEnd ℂ (u1 x) * (L.r x : ℂ)) +
              γ2 * (starRingEnd ℂ (w x - u x) * starRingEnd ℂ (u2 x) * (L.r x : ℂ)))) :=
          setIntegral_congr_fun measurableSet_Ioc (fun x _ => by simp only [hψd]; ring)
        rw [e, integral_sub (I_m hχ0) i12, integral_add i1 i2, integral_const_mul,
          integral_const_mul]
      try simp only [Pi.sub_apply] at hwk
      rw [this] at hwk
      exact sub_eq_zero.mp hwk
    have i0 := I_m hχ0
    have j1 : IntegrableOn (fun x => A * (u1 x * χ0 x * (L.r x : ℂ))) (Ioc c d) :=
      (I_c (hu1.mul hχ0)).const_mul A
    have j2 : IntegrableOn (fun x => B * (u2 x * χ0 x * (L.r x : ℂ))) (Ioc c d) :=
      (I_c (hu2.mul hχ0)).const_mul B
    have j12 : IntegrableOn (fun x => A * (u1 x * χ0 x * (L.r x : ℂ)) +
        B * (u2 x * χ0 x * (L.r x : ℂ))) (Ioc c d) := j1.add j2
    have : ∫ x in Ioc c d, (starRingEnd ℂ (w x - u x) - A * u1 x - B * u2 x) * (g x : ℂ) *
        (L.r x : ℂ) = (∫ x in Ioc c d, starRingEnd ℂ (w x - u x) * χ0 x * (L.r x : ℂ)) -
          (A * p1 + B * p2) := by
      have e : ∫ x in Ioc c d, (starRingEnd ℂ (w x - u x) - A * u1 x - B * u2 x) * (g x : ℂ) *
          (L.r x : ℂ) = ∫ x in Ioc c d, (starRingEnd ℂ (w x - u x) * χ0 x * (L.r x : ℂ) -
            (A * (u1 x * χ0 x * (L.r x : ℂ)) + B * (u2 x * χ0 x * (L.r x : ℂ)))) :=
        setIntegral_congr_fun measurableSet_Ioc (fun x _ => by simp only [hχ0d]; ring)
      rw [e, integral_sub i0 j12, integral_add j1 j2, integral_const_mul, integral_const_mul,
        hp1def, hp2def]
    rw [this, E]
    rw [hγ1, hγ2, hp1def, hp2def]
    simp only [A, B]
    field_simp
    ring
  -- conclude with the fundamental lemma of the calculus of variations
  set f : ℝ → ℂ := (Ioc c d).indicator
    (fun x => (starRingEnd ℂ (w x - u x) - A * u1 x - B * u2 x) * (L.r x : ℂ))
  have hfi : Integrable f := by
    refine (integrable_indicator_iff measurableSet_Ioc).mpr ?_
    have := ((I_m (φ := fun _ => (1 : ℂ)) continuousOn_const).sub
      ((I_c hu1).const_mul A)).sub ((I_c hu2).const_mul B)
    refine IntegrableOn.congr_fun this (fun x _ => ?_) measurableSet_Ioc
    simp only [Pi.sub_apply]; ring
  have hz := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) (U := Ioo c d)
    (hfi.locallyIntegrable.locallyIntegrableOn _) (fun g hg _ _ => by
      have e : (fun x => g x • f x) = (Ioc c d).indicator (fun x =>
          (starRingEnd ℂ (w x - u x) - A * u1 x - B * u2 x) * (g x : ℂ) * (L.r x : ℂ)) := by
        funext x
        by_cases hx : x ∈ Ioc c d
        · simp only [f, indicator_of_mem hx, Complex.real_smul]; ring
        · simp [f, indicator_of_notMem hx]
      rw [e, integral_indicator measurableSet_Ioc]
      exact key g hg.continuous)
  refine ⟨A, B, (ae_restrict_iff' measurableSet_Ioo).mpr (hz.mono fun x hx hmem => ?_)⟩
  have hx' := hx hmem
  have hxI : x ∈ L.I := Icc_sub_I L hc hd (Ioo_subset_Icc_self hmem)
  simp only [f, indicator_of_mem (Ioo_subset_Ioc_self hmem)] at hx'
  rcases mul_eq_zero.mp hx' with h | h
  · linear_combination h
  · exact absurd h (r_ne L hxI)

end SAAux

namespace SAAux

open TeschlQM.SturmLiouville VoCAux LagAux IvpAux WeylAux

/-- **Local regularity.** If `⟨w, τ f⟩ = ⟨k, f⟩` for every compactly supported `f ∈ D(τ)`, then `w`
agrees almost everywhere with a solution of `τ w' = k`. -/
theorem weak_regular (L : SLData) {w k : ℝ → ℂ} (hw : MemLp w 2 L.measure)
    (hk : MemLp k 2 L.measure) (H : WeakHyp L w k) :
    ∃ w' : ℝ → ℂ, w' =ᵐ[L.measure] w ∧ SolvesTau L w' k := by
  obtain ⟨u1, u2, h1, h2, hW⟩ := fund_system L 0
  have hu1 := sol_contOn L h1
  have hu2 := sol_contOn L h2
  obtain ⟨c0, hc0⟩ := exists_mem_I L
  obtain ⟨F, hF, -, -⟩ := IvpAux.ivp L k (rk_loc L hk) c0 hc0 0 0
  have hu : IsSolution L 0 k (F 0) := (hF 0).1
  set u := F 0
  obtain ⟨s0, t0, hs0, ht0, hs0I, ht0I⟩ := exists_Icc_subset_I L hc0
  have hst0 : s0 < t0 := hs0.trans ht0
  obtain ⟨A0, B0, hAB0⟩ := local_rep L hw hk hu h1 h2 hW H hs0I ht0I hst0
  have huniq : ∀ c d : ℝ, c ≤ s0 → t0 ≤ d → ∀ A B : ℂ,
      (∀ᵐ x ∂(volume.restrict (Ioo c d)), starRingEnd ℂ (w x - u x) = A * u1 x + B * u2 x) →
      A = A0 ∧ B = B0 := by
    intro c d hcs htd A B hAB
    have h1' := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hcs htd) hAB
    have heq : (fun x => A * u1 x + B * u2 x) =ᵐ[volume.restrict (Ioo s0 t0)]
        (fun x => A0 * u1 x + B0 * u2 x) := by
      filter_upwards [h1', hAB0] with x e1 e2
      rw [← e1, ← e2]
    have hsub : Ioo s0 t0 ⊆ L.I := Ioo_subset_Icc_self.trans (Icc_sub_I L hs0I ht0I)
    have hcont := Measure.eqOn_open_of_ae_eq heq isOpen_Ioo
      (((continuousOn_const.mul hu1).add (continuousOn_const.mul hu2)).mono hsub)
      (((continuousOn_const.mul hu1).add (continuousOn_const.mul hu2)).mono hsub)
    have := indep_on_interval L h1 h2 hW hs0I ht0I hst0 (A - A0) (B - B0) (fun x hx => by
      have e := hcont hx
      simp only at e
      linear_combination e)
    exact ⟨sub_eq_zero.mp this.1, sub_eq_zero.mp this.2⟩
  have hglob : ∀ᵐ x ∂(volume.restrict L.I),
      starRingEnd ℂ (w x - u x) = A0 * u1 x + B0 * u2 x := by
    refine ae_I_of_local L (fun s t hs ht hst => ?_)
    have hc : min s s0 ∈ L.I := by
      rcases min_choice s s0 with h | h <;> rw [h] <;> assumption
    have hd : max t t0 ∈ L.I := by
      rcases max_choice t t0 with h | h <;> rw [h] <;> assumption
    have hcd : min s s0 < max t t0 := (min_le_left _ _).trans_lt (hst.trans_le (le_max_left _ _))
    obtain ⟨A, B, hAB⟩ := local_rep L hw hk hu h1 h2 hW H hc hd hcd
    obtain ⟨rfl, rfl⟩ := huniq _ _ (min_le_right _ _) (le_max_right _ _) A B hAB
    exact ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo (min_le_left _ _)
      (le_max_left _ _)) hAB
  -- the solution `S` and the representative `w' = u + conj S`
  obtain ⟨hS0, -⟩ := WeylLP.isSolution_lin L h1 h2 A0 B0
  have e0 : (fun x => A0 * (0 : ℝ → ℂ) x + B0 * (0 : ℝ → ℂ) x) = 0 := by funext x; simp
  rw [e0] at hS0
  have hs := solvesTau_conj L hS0
  have hsum := solvesTau_add L hu hs
  have eR : (fun x => (0 * u x + k x) + starRingEnd ℂ (0 * (A0 * u1 x + B0 * u2 x) +
      (0 : ℝ → ℂ) x)) = k := by funext x; simp
  rw [eR] at hsum
  refine ⟨_, ae_of_ae_vol L (hglob.mono fun x hx => ?_), hsum⟩
  have := congrArg (starRingEnd ℂ) hx
  simp only [Complex.conj_conj] at this
  show u x + starRingEnd ℂ (A0 * u1 x + B0 * u2 x) = w x
  rw [← this]; ring

end SAAux

end SecSA3

section SecBcR

/-! Right-endpoint version of Teschl, Lemma 9.5. -/

open MeasureTheory Set Filter Topology
open TeschlQM.SturmLiouville

namespace BcAuxR

theorem W_conj_right (L : SLData) {f g : ℝ → ℂ} (hf : InMaxDomain L f) (hg : InMaxDomain L g) :
    wronskianRight L (fun x => starRingEnd ℂ (g x)) (fun x => starRingEnd ℂ (f x)) =
      starRingEnd ℂ (wronskianRight L g f) := by
  have t1 := SAAux.tendsto_W_right L (BcAux.maxDomain_conj L hf) (BcAux.maxDomain_conj L hg)
  have t2 := (Complex.continuous_conj.tendsto _).comp (SAAux.tendsto_W_right L hf hg)
  refine tendsto_nhds_unique t1 (t2.congr' ?_)
  filter_upwards [LagAux.eventually_mem_right L] with x hx
  obtain ⟨-, F, hF, -⟩ := hf
  obtain ⟨-, G, hG, -⟩ := hg
  simp only [Function.comp, wronskian]
  rw [LagAux.quasiDeriv_conj L hF.1 x hx, LagAux.quasiDeriv_conj L hG.1 x hx]
  simp

theorem W_anti_right (L : SLData) {f g : ℝ → ℂ} (hf : InMaxDomain L f) (hg : InMaxDomain L g) :
    wronskianRight L g f = -wronskianRight L f g := by
  have t1 := SAAux.tendsto_W_right L hf hg
  have t2 := (SAAux.tendsto_W_right L hg hf).neg
  refine tendsto_nhds_unique t1 (t2.congr' (Eventually.of_forall fun x => ?_))
  simp only [wronskian]; ring

theorem plucker_right (L : SLData) {f1 f2 f3 f4 : ℝ → ℂ} (h1 : InMaxDomain L f1)
    (h2 : InMaxDomain L f2) (h3 : InMaxDomain L f3) (h4 : InMaxDomain L f4) :
    wronskianRight L f1 f2 * wronskianRight L f3 f4 + wronskianRight L f1 f3 * wronskianRight L f4 f2 +
      wronskianRight L f1 f4 * wronskianRight L f2 f3 = 0 := by
  have t := (((SAAux.tendsto_W_right L h2 h1).mul (SAAux.tendsto_W_right L h4 h3)).add
    ((SAAux.tendsto_W_right L h3 h1).mul (SAAux.tendsto_W_right L h2 h4))).add
    ((SAAux.tendsto_W_right L h4 h1).mul (SAAux.tendsto_W_right L h3 h2))
  refine tendsto_nhds_unique t (tendsto_const_nhds.congr' (Eventually.of_forall fun x => ?_))
  simp only [wronskian]; ring

end BcAuxR

theorem BcAuxR.wronskian_bc_symmetric_right (L : SLData) (v fhat : ℝ → ℂ) (hv : InMaxDomain L v)
    (hvv : wronskianRight L (fun x => starRingEnd ℂ (v x)) v = 0)
    (hfhat : InMaxDomain L fhat)
    (hne : wronskianRight L (fun x => starRingEnd ℂ (v x)) fhat ≠ 0)
    (f g : ℝ → ℂ) (hf : InMaxDomain L f) (hg : InMaxDomain L g) :
    (wronskianRight L v f = 0 ↔ wronskianRight L v (fun x => starRingEnd ℂ (f x)) = 0) ∧
      (wronskianRight L v f = 0 → wronskianRight L v g = 0 →
        wronskianRight L (fun x => starRingEnd ℂ (g x)) f = 0) := by
  have hvc := BcAux.maxDomain_conj L hv
  have hvv' : wronskianRight L v (fun x => starRingEnd ℂ (v x)) = 0 := by
    rw [BcAuxR.W_anti_right L hvc hv, hvv, neg_zero]
  -- `W_a(v, f̂) ≠ 0`
  have hvf : wronskianRight L v fhat ≠ 0 := by
    intro h0
    have hfc := BcAux.maxDomain_conj L hfhat
    have P := BcAuxR.plucker_right L hv hfc hvc hfhat
    rw [hvv', h0] at P
    simp only [zero_mul, add_zero] at P
    rcases mul_eq_zero.mp P with h | h
    · have := BcAuxR.W_conj_right L hfc hv
      rw [BcAux.conj_conj_fun, h, map_zero] at this
      exact hne this
    · exact hne h
  -- forward direction of (9.15), in the form `W_a(v, h) = 0 → W_a(v*, h) = 0`
  have fwd : ∀ h : ℝ → ℂ, InMaxDomain L h → wronskianRight L v h = 0 →
      wronskianRight L (fun x => starRingEnd ℂ (v x)) h = 0 := by
    intro h hh h0
    have P := BcAuxR.plucker_right L hv hh hvc hfhat
    rw [h0, hvv'] at P
    simp only [zero_mul, add_zero, zero_add] at P
    rcases mul_eq_zero.mp P with h1 | h1
    · exact absurd h1 hvf
    · rw [BcAuxR.W_anti_right L hh hvc, h1, neg_zero]
  have fwd' : ∀ h : ℝ → ℂ, InMaxDomain L h → wronskianRight L v h = 0 →
      wronskianRight L v (fun x => starRingEnd ℂ (h x)) = 0 := by
    intro h hh h0
    have := BcAuxR.W_conj_right L hh hvc
    rw [BcAux.conj_conj_fun, fwd h hh h0, map_zero] at this
    exact this
  refine ⟨⟨fwd' f hf, fun h0 => ?_⟩, fun h1 h2 => ?_⟩
  · have := fwd' _ (BcAux.maxDomain_conj L hf) h0
    rwa [BcAux.conj_conj_fun] at this
  · have hgc := BcAux.maxDomain_conj L hg
    have P := BcAuxR.plucker_right L hv hfhat hf hgc
    rw [h1, fwd' g hg h2] at P
    simp only [zero_mul, add_zero, zero_mul] at P
    rcases mul_eq_zero.mp P with h3 | h3
    · exact absurd h3 hvf
    · rw [BcAuxR.W_anti_right L hf hgc, h3, neg_zero]

end SecBcR

section SecSAAbs

/-!
# An abstract criterion for self-adjointness and cores

If `T ≤ S`, `T` is densely defined, `S` is symmetric and every pair `(y, q)` with
`⟪q, x⟫ = ⟪y, T x⟫` for all `x ∈ 𝔇(T)` lies in the graph of `S` (i.e. `T* ≤ S`), then `S` is
self-adjoint and the closure of `T` is `S`.
-/

open scoped InnerProductSpace
open LinearPMap WithLp

namespace SAAbs

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem selfAdjoint_and_closure (T S : H →ₗ.[ℂ] H) (hTS : T ≤ S)
    (hT : Dense (T.domain : Set H))
    (hS : ∀ x y : S.domain, ⟪S x, (y : H)⟫_ℂ = ⟪(x : H), S y⟫_ℂ)
    (hadj : ∀ y q : H, (∀ x : T.domain, ⟪q, (x : H)⟫_ℂ = ⟪y, T x⟫_ℂ) →
      ∃ h : y ∈ S.domain, S ⟨y, h⟩ = q) :
    IsSelfAdjoint S ∧ T.closure = S := by
  have hSd : Dense (S.domain : Set H) := hT.mono hTS.1
  -- `S† = S`
  have hSS : S† = S := by
    apply le_antisymm
    · refine ⟨fun y hy => ?_, fun y x hxy => ?_⟩
      · obtain ⟨h, -⟩ := hadj y (S† ⟨y, hy⟩) (fun x => by
          rw [adjoint_isFormalAdjoint hSd ⟨y, hy⟩ ⟨x, hTS.1 x.2⟩]
          congr 1
          exact (hTS.2 rfl).symm)
        exact h
      · obtain ⟨h, hq⟩ := hadj (y : H) (S† y) (fun x => by
          rw [adjoint_isFormalAdjoint hSd y ⟨x, hTS.1 x.2⟩]
          congr 1
          exact (hTS.2 rfl).symm)
        rw [← hq]
        congr 1
        exact Subtype.ext hxy
    · exact IsFormalAdjoint.le_adjoint hSd (fun x y => hS x y)
  refine ⟨hSS, ?_⟩
  have hSc : S.IsClosed := by rw [← hSS]; exact adjoint_isClosed hSd
  have hTc : T.IsClosable := IsClosable.leIsClosable hSc.isClosable hTS
  apply eq_of_eq_graph
  rw [← hTc.graph_closure_eq_closure_graph]
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ (le_graph_iff.mpr hTS) hSc
  · intro p hp
    -- transport to the Hilbert space `WithLp 2 (H × H)`
    let K : Submodule ℂ (WithLp 2 (H × H)) := T.graph.comap (WithLp.linearEquiv 2 ℂ (H × H)).toLinearMap
    have key : toLp 2 p ∈ Kᗮᗮ := by
      rw [Submodule.mem_orthogonal]
      intro q hq
      rw [Submodule.mem_orthogonal] at hq
      have horth : ∀ z : T.domain, ⟪(z : H), (ofLp q).1⟫_ℂ + ⟪T z, (ofLp q).2⟫_ℂ = 0 := by
        intro z
        have := hq (toLp 2 ((z : H), T z)) (by
          show (WithLp.linearEquiv 2 ℂ (H × H)) (toLp 2 ((z : H), T z)) ∈ T.graph
          simp [LinearPMap.mem_graph_iff])
        simpa using this
      obtain ⟨h2, hS2⟩ := hadj (ofLp q).2 (-(ofLp q).1) (fun z => by
        have e := horth z
        rw [inner_neg_left, ← inner_conj_symm, ← inner_conj_symm (ofLp q).2]
        rw [add_eq_zero_iff_eq_neg] at e
        rw [e, _root_.map_neg, neg_neg])
      rw [LinearPMap.mem_graph_iff] at hp
      obtain ⟨x, hpx1, hpx⟩ := hp
      obtain ⟨p1, p2⟩ := p
      simp only at hpx1 hpx
      subst hpx1
      simp only [WithLp.prod_inner_apply]
      have e1 : (ofLp q).1 = -(S ⟨(ofLp q).2, h2⟩) := by rw [hS2, neg_neg]
      rw [e1, inner_neg_left, ← hpx, hS ⟨(ofLp q).2, h2⟩ x]
      simp
    rw [Submodule.orthogonal_orthogonal_eq_closure] at key
    have hcont : Continuous (fun v : WithLp 2 (H × H) => ofLp v) := WithLp.prod_continuous_ofLp 2 H H
    have hsub : (K.topologicalClosure : Set (WithLp 2 (H × H))) ⊆
        (fun v => ofLp v) ⁻¹' (T.graph.topologicalClosure : Set (H × H)) := by
      rw [Submodule.topologicalClosure_coe]
      refine closure_minimal (fun v hv => ?_) ((Submodule.isClosed_topologicalClosure _).preimage hcont)
      exact Submodule.le_topologicalClosure _ hv
    have := hsub key
    first
      | exact this
      | simpa using this
      | simpa [← Submodule.topologicalClosure_coe] using this

end SAAbs

end SecSAAbs

section SecSA4

/-!
# Teschl, Theorem 9.6: self-adjointness of the operator with separated boundary conditions
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace SAAux

open TeschlQM.SturmLiouville VoCAux LagAux IvpAux WeylAux

theorem W_self_left (L : SLData) (f : ℝ → ℂ) : wronskianLeft L f f = 0 :=
  wronskianLeft_of_eventually L (Eventually.of_forall fun x => by unfold wronskian; ring)

theorem W_self_right (L : SLData) (f : ℝ → ℂ) : wronskianRight L f f = 0 :=
  wronskianRight_of_eventually L (Eventually.of_forall fun x => by unfold wronskian; ring)

theorem wLeft_congr (L : SLData) {a b a' b' : ℝ → ℂ}
    (h : ∀ᶠ x in L.atLeft, wronskian L x a b = wronskian L x a' b') :
    wronskianLeft L a b = wronskianLeft L a' b' := by
  unfold wronskianLeft
  exact congrArg lim (Filter.map_congr h)

theorem wRight_congr (L : SLData) {a b a' b' : ℝ → ℂ}
    (h : ∀ᶠ x in L.atRight, wronskian L x a b = wronskian L x a' b') :
    wronskianRight L a b = wronskianRight L a' b' := by
  unfold wronskianRight
  exact congrArg lim (Filter.map_congr h)

/-- Real and imaginary parts of an element of `D(τ)`. -/
theorem re_im_parts (L : SLData) {f : ℝ → ℂ} (hf : InMaxDomain L f) :
    ∃ fr fi : ℝ → ℂ, InMaxDomain L fr ∧ InMaxDomain L fi ∧
      (fun x => starRingEnd ℂ (fr x)) = fr ∧ (fun x => starRingEnd ℂ (fi x)) = fi ∧
      (fun x => fr x + Complex.I * fi x) = f := by
  have hfc := BcAux.maxDomain_conj L hf
  refine ⟨fun x => (1 / 2 : ℂ) * f x + (1 / 2 : ℂ) * starRingEnd ℂ (f x),
    fun x => (-Complex.I / 2) * f x + (Complex.I / 2) * starRingEnd ℂ (f x),
    inMax_add L (inMax_smul L hf _) (inMax_smul L hfc _),
    inMax_add L (inMax_smul L hf _) (inMax_smul L hfc _), ?_, ?_, ?_⟩
  · funext x; simp only [map_add, map_mul, Complex.conj_conj, map_div₀, map_one, map_ofNat]
    ring
  · funext x
    simp only [map_add, map_mul, Complex.conj_conj, map_div₀, map_neg, Complex.conj_I, map_ofNat]
    ring
  · funext x; ring_nf; rw [Complex.I_sq]; ring

/-- At a limit point endpoint all boundary Wronskians vanish. -/
theorem lp_W_zero_left (L : SLData) (hlp : ¬ IsLimitCircleLeft L) {f g : ℝ → ℂ}
    (hf : InMaxDomain L f) (hg : InMaxDomain L g) : wronskianLeft L f g = 0 := by
  by_contra hne
  apply hlp
  obtain ⟨fr, fi, hr, hi, cr, ci, e⟩ := re_im_parts L hf
  have hgf : wronskianLeft L g f = wronskianLeft L g fr + Complex.I * wronskianLeft L g fi := by
    rw [← wLeft_smul L hg hi, ← wLeft_add L hg hr (inMax_smul L hi _), e]
  have hne' : wronskianLeft L g f ≠ 0 := by
    rw [BcAux.W_anti_left L hf hg]; exact neg_ne_zero.mpr hne
  by_cases h1 : wronskianLeft L g fr = 0
  · have h2 : wronskianLeft L g fi ≠ 0 := by
      intro h2; apply hne'; rw [hgf, h1, h2]; ring
    refine ⟨fi, hi, by rw [ci]; exact W_self_left L fi, g, hg, ?_⟩
    rw [BcAux.W_anti_left L hg hi]; exact neg_ne_zero.mpr h2
  · refine ⟨fr, hr, by rw [cr]; exact W_self_left L fr, g, hg, ?_⟩
    rw [BcAux.W_anti_left L hg hr]; exact neg_ne_zero.mpr h1

theorem lp_W_zero_right (L : SLData) (hlp : ¬ IsLimitCircleRight L) {f g : ℝ → ℂ}
    (hf : InMaxDomain L f) (hg : InMaxDomain L g) : wronskianRight L f g = 0 := by
  by_contra hne
  apply hlp
  obtain ⟨fr, fi, hr, hi, cr, ci, e⟩ := re_im_parts L hf
  have hgf : wronskianRight L g f = wronskianRight L g fr + Complex.I * wronskianRight L g fi := by
    rw [← wRight_smul L hg hi, ← wRight_add L hg hr (inMax_smul L hi _), e]
  have hne' : wronskianRight L g f ≠ 0 := by
    rw [BcAuxR.W_anti_right L hf hg]; exact neg_ne_zero.mpr hne
  by_cases h1 : wronskianRight L g fr = 0
  · have h2 : wronskianRight L g fi ≠ 0 := by
      intro h2; apply hne'; rw [hgf, h1, h2]; ring
    refine ⟨fi, hi, by rw [ci]; exact W_self_right L fi, g, hg, ?_⟩
    rw [BcAuxR.W_anti_right L hg hi]; exact neg_ne_zero.mpr h2
  · refine ⟨fr, hr, by rw [cr]; exact W_self_right L fr, g, hg, ?_⟩
    rw [BcAuxR.W_anti_right L hg hr]; exact neg_ne_zero.mpr h1

/-- The boundary terms vanish on the domain `𝔇(A)`. -/
theorem bc_W_zero_left (L : SLData) {v w f g : ℝ → ℂ} (H : BcHyp L v w)
    (hf : bcDomain L v w f) (hg : bcDomain L v w g) :
    wronskianLeft L (fun x => starRingEnd ℂ (g x)) f = 0 := by
  by_cases hl : IsLimitCircleLeft L
  · obtain ⟨hv, hvv, f0, hf0, hne⟩ := H.1 hl
    have hne' : wronskianLeft L (fun x => starRingEnd ℂ (v x)) (fun x => starRingEnd ℂ (f0 x))
        ≠ 0 := by
      rw [BcAux.W_conj_left L hf0 hv]; exact (map_ne_zero _).mpr hne
    exact (BcAux.wronskian_bc_symmetric L v _ hv hvv (BcAux.maxDomain_conj L hf0) hne' f g hf.1
      hg.1).2 (hf.2.1 hl) (hg.2.1 hl)
  · exact lp_W_zero_left L hl (BcAux.maxDomain_conj L hg.1) hf.1

theorem bc_W_zero_right (L : SLData) {v w f g : ℝ → ℂ} (H : BcHyp L v w)
    (hf : bcDomain L v w f) (hg : bcDomain L v w g) :
    wronskianRight L (fun x => starRingEnd ℂ (g x)) f = 0 := by
  by_cases hr : IsLimitCircleRight L
  · obtain ⟨hw, hww, f0, hf0, hne⟩ := H.2 hr
    have hne' : wronskianRight L (fun x => starRingEnd ℂ (w x)) (fun x => starRingEnd ℂ (f0 x))
        ≠ 0 := by
      rw [BcAuxR.W_conj_right L hf0 hw]; exact (map_ne_zero _).mpr hne
    exact (BcAuxR.wronskian_bc_symmetric_right L w _ hw hww (BcAux.maxDomain_conj L hf0) hne' f g
      hf.1 hg.1).2 (hf.2.2 hr) (hg.2.2 hr)
  · exact lp_W_zero_right L hr (BcAux.maxDomain_conj L hg.1) hf.1

/-! ### Inner products and graph membership -/

theorem inner_Lp_toLp (L : SLData) (y : Lp ℂ 2 L.measure) {g : ℝ → ℂ}
    (hg : MemLp g 2 L.measure) :
    ⟪y, hg.toLp g⟫_ℂ = ∫ x, starRingEnd ℂ (y x) * g x ∂L.measure := by
  rw [L2.inner_def]
  refine integral_congr_ae (hg.coeFn_toLp.mono fun x hx => ?_)
  simp only [RCLike.inner_apply, hx]
  ring

theorem inner_toLp (L : SLData) {f g : ℝ → ℂ} (hf : MemLp f 2 L.measure)
    (hg : MemLp g 2 L.measure) :
    ⟪hf.toLp f, hg.toLp g⟫_ℂ = ∫ x, starRingEnd ℂ (f x) * g x ∂L.measure := by
  rw [inner_Lp_toLp]
  refine integral_congr_ae (hf.coeFn_toLp.mono fun x hx => ?_)
  simp only [hx]

theorem graph_mem (L : SLData) {D : (ℝ → ℂ) → Prop} {A : Lp ℂ 2 L.measure →ₗ.[ℂ] Lp ℂ 2 L.measure}
    (hA : (A.graph : Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure)) = operatorGraph L D)
    {f F : ℝ → ℂ} (hf2 : MemLp f 2 L.measure) (hF2 : MemLp F 2 L.measure) (hD : D f)
    (hs : SolvesTau L f F) : ∃ y : A.domain, (y : Lp ℂ 2 L.measure) = hf2.toLp f ∧
      A y = hF2.toLp F := by
  have : (hf2.toLp f, hF2.toLp F) ∈ (A.graph : Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure)) := by
    rw [hA]; exact ⟨f, F, hf2, hF2, hD, hs, rfl⟩
  exact (LinearPMap.mem_graph_iff A).mp this

theorem graph_of_dom (L : SLData) {D : (ℝ → ℂ) → Prop}
    {A : Lp ℂ 2 L.measure →ₗ.[ℂ] Lp ℂ 2 L.measure}
    (hA : (A.graph : Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure)) = operatorGraph L D)
    (x : A.domain) : ∃ (f F : ℝ → ℂ) (hf2 : MemLp f 2 L.measure) (hF2 : MemLp F 2 L.measure),
      D f ∧ SolvesTau L f F ∧ (x : Lp ℂ 2 L.measure) = hf2.toLp f ∧ A x = hF2.toLp F := by
  have : ((x : Lp ℂ 2 L.measure), A x) ∈
      (A.graph : Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure)) := A.mem_graph x
  rw [hA] at this
  obtain ⟨f, F, hf2, hF2, hD, hs, he⟩ := this
  simp only [Prod.mk.injEq] at he
  exact ⟨f, F, hf2, hF2, hD, hs, he.1, he.2⟩

/-- Symmetry of the operator with domain `𝔇(A)`. -/
theorem symm_A (L : SLData) {v w : ℝ → ℂ} (H : BcHyp L v w)
    (A : Lp ℂ 2 L.measure →ₗ.[ℂ] Lp ℂ 2 L.measure)
    (hA : (A.graph : Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure)) =
      operatorGraph L (bcDomain L v w)) :
    ∀ x y : A.domain, ⟪A x, (y : Lp ℂ 2 L.measure)⟫_ℂ = ⟪(x : Lp ℂ 2 L.measure), A y⟫_ℂ := by
  intro x y
  obtain ⟨f, F, hf2, hF2, hDf, hsf, hx1, hx2⟩ := graph_of_dom L hA x
  obtain ⟨g, G, hg2, hG2, hDg, hsg, hy1, hy2⟩ := graph_of_dom L hA y
  rw [hx2, hy1, hx1, hy2, inner_toLp, inner_toLp]
  have lag := lagrange_identity_aux L g f G F hg2 hf2 hsg hsf hG2 hF2
  rw [lag.2.2.2.2, bc_W_zero_left L H hDg hDf, bc_W_zero_right L H hDg hDf]
  ring

/-! ### Density and the adjoint inclusion -/

theorem test_core (L : SLData) {v w : ℝ → ℂ} {A₁ : Lp ℂ 2 L.measure →ₗ.[ℂ] Lp ℂ 2 L.measure}
    (hA₁ : (A₁.graph : Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure)) =
      operatorGraph L (coreDomain L v w))
    {c d : ℝ} (hc : c ∈ L.I) (hd : d ∈ L.I) {f F : ℝ → ℂ} (hs : SolvesTau L f F)
    (hf2 : MemLp f 2 L.measure) (hF2 : MemLp F 2 L.measure)
    (hl : ∀ x ∈ L.I, x ≤ c → f x = 0 ∧ quasiDeriv L f x = 0)
    (hr : ∀ x ∈ L.I, d ≤ x → f x = 0 ∧ quasiDeriv L f x = 0) :
    ∃ y : A₁.domain, (y : Lp ℂ 2 L.measure) = hf2.toLp f ∧ A₁ y = hF2.toLp F :=
  graph_mem L hA₁ hf2 hF2 (compact_core L ⟨hf2, F, hs, hF2⟩ hc hd hl hr) hs

theorem dense_core (L : SLData) {v w : ℝ → ℂ} (A₁ : Lp ℂ 2 L.measure →ₗ.[ℂ] Lp ℂ 2 L.measure)
    (hA₁ : (A₁.graph : Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure)) =
      operatorGraph L (coreDomain L v w)) : Dense (A₁.domain : Set (Lp ℂ 2 L.measure)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro z hz
  rw [Submodule.mem_orthogonal] at hz
  have H : WeakHyp L 0 z := by
    intro c d hc hd _ f F hs hf2 hF2 hl hr
    obtain ⟨y, hy1, -⟩ := test_core L hA₁ hc hd hs hf2 hF2 hl hr
    have e := hz y y.2
    rw [hy1, ← inner_conj_symm, inner_Lp_toLp, map_eq_zero] at e
    rw [e]; simp
  obtain ⟨w', hw', hs⟩ := weak_regular L MemLp.zero (Lp.memLp z) H
  have hw0 := eqOn_of_ae L (tau_contOn L hs) continuousOn_const hw'
  have hs0 : SolvesTau L (0 : ℝ → ℂ) z := solvesTau_congr L hw0 hs
  rw [Lp.eq_zero_iff_ae_eq_zero]
  exact tau_unique L hs0 (solvesTau_zero L)

/-- `A₁* ⊆ A`. -/
theorem adj_core (L : SLData) {v w : ℝ → ℂ} (H : BcHyp L v w)
    (A A₁ : Lp ℂ 2 L.measure →ₗ.[ℂ] Lp ℂ 2 L.measure)
    (hA : (A.graph : Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure)) =
      operatorGraph L (bcDomain L v w))
    (hA₁ : (A₁.graph : Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure)) =
      operatorGraph L (coreDomain L v w)) :
    ∀ y q : Lp ℂ 2 L.measure, (∀ x : A₁.domain, ⟪q, (x : Lp ℂ 2 L.measure)⟫_ℂ = ⟪y, A₁ x⟫_ℂ) →
      ∃ h : y ∈ A.domain, A ⟨y, h⟩ = q := by
  intro y q hyq
  -- the weak equation
  have key : ∀ (f F : ℝ → ℂ) (hf2 : MemLp f 2 L.measure) (hF2 : MemLp F 2 L.measure)
      (x : A₁.domain), (x : Lp ℂ 2 L.measure) = hf2.toLp f → A₁ x = hF2.toLp F →
      ∫ x, starRingEnd ℂ (y x) * F x ∂L.measure = ∫ x, starRingEnd ℂ (q x) * f x ∂L.measure := by
    intro f F hf2 hF2 x hx1 hx2
    have e := hyq x
    rw [hx1, hx2, inner_Lp_toLp, inner_Lp_toLp] at e
    exact e.symm
  have HW : WeakHyp L y q := by
    intro c d hc hd _ f F hs hf2 hF2 hl hr
    obtain ⟨x, hx1, hx2⟩ := test_core L hA₁ hc hd hs hf2 hF2 hl hr
    exact key f F hf2 hF2 x hx1 hx2
  obtain ⟨w', hw', hs⟩ := weak_regular L (Lp.memLp y) (Lp.memLp q) HW
  have hw'2 : MemLp w' 2 L.measure := (Lp.memLp y).ae_eq hw'.symm
  have hmax : InMaxDomain L w' := ⟨hw'2, q, hs, Lp.memLp q⟩
  have hmaxc := BcAux.maxDomain_conj L hmax
  have hint : ∀ (f F : ℝ → ℂ), MemLp f 2 L.measure → MemLp F 2 L.measure →
      ∫ x, starRingEnd ℂ (y x) * F x ∂L.measure =
        ∫ x, starRingEnd ℂ (w' x) * F x ∂L.measure := by
    intro f F _ _
    refine integral_congr_ae (hw'.mono fun x hx => ?_)
    simp only [hx]
  obtain ⟨c, hc⟩ := exists_mem_I L
  have hbc : bcDomain L v w w' := by
    refine ⟨hmax, fun hl => ?_, fun hr => ?_⟩
    · obtain ⟨hv, hvv, f0, hf0, hne⟩ := H.1 hl
      obtain ⟨hv2, V, hV, hV2⟩ := hv
      obtain ⟨fv, Fv, d, hd, hcd, hsv, hfv2, hFv2, hle, hge⟩ := cutoff_left L hV hv2 hV2 hc
      have hcore : coreDomain L v w fv := by
        refine ⟨⟨hfv2, Fv, hsv, hFv2⟩, fun _ => ⟨c, hc, fun x hx hlt => ?_⟩,
          fun _ => ⟨d, hd, fun x hx hlt => ?_⟩⟩
        · obtain ⟨e1, e2⟩ := hle x hx hlt.le
          unfold wronskian; rw [e1, e2]; ring
        · obtain ⟨e1, e2⟩ := hge x hx hlt.le
          unfold wronskian; rw [e1, e2]; ring
      obtain ⟨x, hx1, hx2⟩ := graph_mem L hA₁ hfv2 hFv2 hcore hsv
      have e := key fv Fv hfv2 hFv2 x hx1 hx2
      rw [hint fv Fv hfv2 hFv2] at e
      have lag := (lagrange_identity_aux L fv w' Fv q hfv2 hw'2 hsv hs hFv2 (Lp.memLp q)).2.2.2.2
      have hWb : wronskianRight L (fun x => starRingEnd ℂ (w' x)) fv = 0 :=
        wronskianRight_of_eventually L (((eventually_mem_right L).and
          (eventually_gt_right L hd.2)).mono fun x hx => by
            obtain ⟨e1, e2⟩ := hge x hx.1 hx.2.le
            unfold wronskian; rw [e1, e2]; ring)
      rw [hWb, sub_zero, e] at lag
      have hWa : wronskianLeft L (fun x => starRingEnd ℂ (w' x)) fv = 0 := by
        linear_combination -lag
      have hv' : InMaxDomain L v := ⟨hv2, V, hV, hV2⟩
      have hWa' : wronskianLeft L (fun x => starRingEnd ℂ (w' x)) v = 0 := by
        rw [← hWa]
        refine wLeft_congr L (((eventually_mem_left L).and
          (eventually_lt_left L hc.1)).mono fun x hx => ?_)
        obtain ⟨e1, e2⟩ := hle x hx.1 hx.2.le
        unfold wronskian; rw [e1, e2]
      have h3 : wronskianLeft L v (fun x => starRingEnd ℂ (w' x)) = 0 := by
        rw [BcAux.W_anti_left L hmaxc hv', hWa', neg_zero]
      have hne' : wronskianLeft L (fun x => starRingEnd ℂ (v x))
          (fun x => starRingEnd ℂ (f0 x)) ≠ 0 := by
        rw [BcAux.W_conj_left L hf0 hv']; exact (map_ne_zero _).mpr hne
      have := (BcAux.wronskian_bc_symmetric L v _ hv' hvv (BcAux.maxDomain_conj L hf0) hne'
        _ w' hmaxc hmax).1.mp h3
      rwa [BcAux.conj_conj_fun] at this
    · obtain ⟨hw, hww, f0, hf0, hne⟩ := H.2 hr
      obtain ⟨hw2, W, hW, hW2⟩ := hw
      obtain ⟨fw, Fw, d, hd, hdc, hsw, hfw2, hFw2, hge, hle⟩ := cutoff_right L hW hw2 hW2 hc
      have hcore : coreDomain L v w fw := by
        refine ⟨⟨hfw2, Fw, hsw, hFw2⟩, fun _ => ⟨d, hd, fun x hx hlt => ?_⟩,
          fun _ => ⟨c, hc, fun x hx hlt => ?_⟩⟩
        · obtain ⟨e1, e2⟩ := hle x hx hlt.le
          unfold wronskian; rw [e1, e2]; ring
        · obtain ⟨e1, e2⟩ := hge x hx hlt.le
          unfold wronskian; rw [e1, e2]; ring
      obtain ⟨x, hx1, hx2⟩ := graph_mem L hA₁ hfw2 hFw2 hcore hsw
      have e := key fw Fw hfw2 hFw2 x hx1 hx2
      rw [hint fw Fw hfw2 hFw2] at e
      have lag := (lagrange_identity_aux L fw w' Fw q hfw2 hw'2 hsw hs hFw2 (Lp.memLp q)).2.2.2.2
      have hWa : wronskianLeft L (fun x => starRingEnd ℂ (w' x)) fw = 0 :=
        wronskianLeft_of_eventually L (((eventually_mem_left L).and
          (eventually_lt_left L hd.1)).mono fun x hx => by
            obtain ⟨e1, e2⟩ := hle x hx.1 hx.2.le
            unfold wronskian; rw [e1, e2]; ring)
      rw [hWa, zero_sub, e] at lag
      have hWb : wronskianRight L (fun x => starRingEnd ℂ (w' x)) fw = 0 := by
        linear_combination lag
      have hw' : InMaxDomain L w := ⟨hw2, W, hW, hW2⟩
      have hWb' : wronskianRight L (fun x => starRingEnd ℂ (w' x)) w = 0 := by
        rw [← hWb]
        refine wRight_congr L (((eventually_mem_right L).and
          (eventually_gt_right L hc.2)).mono fun x hx => ?_)
        obtain ⟨e1, e2⟩ := hge x hx.1 hx.2.le
        unfold wronskian; rw [e1, e2]
      have h3 : wronskianRight L w (fun x => starRingEnd ℂ (w' x)) = 0 := by
        rw [BcAuxR.W_anti_right L hmaxc hw', hWb', neg_zero]
      have hne' : wronskianRight L (fun x => starRingEnd ℂ (w x))
          (fun x => starRingEnd ℂ (f0 x)) ≠ 0 := by
        rw [BcAuxR.W_conj_right L hf0 hw']; exact (map_ne_zero _).mpr hne
      have := (BcAuxR.wronskian_bc_symmetric_right L w _ hw' hww (BcAux.maxDomain_conj L hf0)
        hne' _ w' hmaxc hmax).1.mp h3
      rwa [BcAux.conj_conj_fun] at this
  have hmem : (y, q) ∈ (A.graph : Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure)) := by
    rw [hA]
    refine ⟨w', q, hw'2, Lp.memLp q, hbc, hs, ?_⟩
    rw [Lp.toLp_coeFn]
    congr 1
    rw [← Lp.toLp_coeFn y (Lp.memLp y)]
    exact (MemLp.toLp_congr _ _ hw').symm
  obtain ⟨z, hz1, hz2⟩ := (LinearPMap.mem_graph_iff A).mp hmem
  have hzy : (z : Lp ℂ 2 L.measure) = y := hz1
  refine ⟨by rw [← hzy]; exact z.2, ?_⟩
  have : A z = q := hz2
  rw [← this]
  congr 1
  exact Subtype.ext hzy.symm

/-- **Teschl, Theorem 9.6.** -/
theorem selfAdjoint_bc (L : SLData) (v w : ℝ → ℂ)
    (hv : IsLimitCircleLeft L → InMaxDomain L v ∧
      wronskianLeft L (fun x => starRingEnd ℂ (v x)) v = 0 ∧
      ∃ f : ℝ → ℂ, InMaxDomain L f ∧ wronskianLeft L v f ≠ 0)
    (hw : IsLimitCircleRight L → InMaxDomain L w ∧
      wronskianRight L (fun x => starRingEnd ℂ (w x)) w = 0 ∧
      ∃ f : ℝ → ℂ, InMaxDomain L f ∧ wronskianRight L w f ≠ 0) :
    ∃ A : Lp ℂ 2 L.measure →ₗ.[ℂ] Lp ℂ 2 L.measure,
      (A.graph : Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure)) =
          operatorGraph L (bcDomain L v w) ∧
        IsSelfAdjoint A ∧
        ∃ A₁ : Lp ℂ 2 L.measure →ₗ.[ℂ] Lp ℂ 2 L.measure,
          (A₁.graph : Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure)) =
              operatorGraph L (coreDomain L v w) ∧
            A₁.closure = A := by
  have H : BcHyp L v w := ⟨hv, hw⟩
  obtain ⟨A, hA⟩ := exists_pmap L (bcDomain L v w) (bc_zero L v w) (bc_add L H) (bc_smul L H)
  obtain ⟨A₁, hA₁⟩ := exists_pmap L (coreDomain L v w) (core_zero L v w) (core_add L) (core_smul L)
  have hle : A₁ ≤ A := by
    refine LinearPMap.le_of_le_graph (fun p hp => ?_)
    have hp' : p ∈ (A₁.graph : Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure)) := hp
    rw [hA₁] at hp'
    obtain ⟨f, g, hf, hg, hD, hs, rfl⟩ := hp'
    show _ ∈ (A.graph : Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure))
    rw [hA]
    exact ⟨f, g, hf, hg, core_bc L hD, hs, rfl⟩
  obtain ⟨hSA, hcl⟩ := SAAbs.selfAdjoint_and_closure A₁ A hle (dense_core L A₁ hA₁)
    (symm_A L H A hA) (adj_core L H A A₁ hA hA₁)
  exact ⟨A, hA, hSA, A₁, hA₁, hcl⟩

end SAAux

end SecSA4

section SecRG1

/-! # Lemma 9.7, part 1: the resolvent, linear combinations, boundary Wronskians -/

open MeasureTheory Set Filter Topology
open scoped Interval

namespace RGAux

open TeschlQM.SturmLiouville VoCAux LagAux IvpAux WeylAux SAAux

/-- A representative of `R φ`. -/
theorem res_rep (L : SLData) {v w : ℝ → ℂ} {A : Lp ℂ 2 L.measure →ₗ.[ℂ] Lp ℂ 2 L.measure}
    (hA : (A.graph : Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure)) =
      operatorGraph L (bcDomain L v w))
    {z : ℂ} {R : Lp ℂ 2 L.measure →L[ℂ] Lp ℂ 2 L.measure} (hR : IsResolventAt A z R)
    {φ : ℝ → ℂ} (hφ : MemLp φ 2 L.measure) :
    ∃ f : ℝ → ℂ, (R (hφ.toLp φ) : ℝ → ℂ) =ᵐ[L.measure] f ∧ bcDomain L v w f ∧
      IsSolution L z φ f := by
  obtain ⟨h, he⟩ := hR.1 (hφ.toLp φ)
  obtain ⟨f, F, hf2, hF2, hD, hs, hx1, hx2⟩ := graph_of_dom L hA ⟨_, h⟩
  refine ⟨f, ?_, hD, ?_⟩
  · have : (R (hφ.toLp φ) : Lp ℂ 2 L.measure) = hf2.toLp f := hx1
    rw [this]; exact hf2.coeFn_toLp
  · rw [hx2] at he
    have hx1' : (R (hφ.toLp φ) : Lp ℂ 2 L.measure) = hf2.toLp f := hx1
    rw [hx1'] at he
    have e : (hφ.toLp φ : ℝ → ℂ) =ᵐ[L.measure] fun x => F x - z * f x := by
      rw [← he]
      filter_upwards [Lp.coeFn_sub (hF2.toLp F) (z • hf2.toLp f), Lp.coeFn_smul z (hf2.toLp f),
        hF2.coeFn_toLp, hf2.coeFn_toLp] with x h1 h2 h3 h4
      rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]
    have e2 : F =ᵐ[L.measure] fun x => z * f x + φ x := by
      filter_upwards [e, hφ.coeFn_toLp] with x h1 h2
      rw [← h2, h1]; ring
    exact solvesTau_congr_rhs L e2 hs

/-- Injectivity of `A - z`: a solution of `(τ - z) u = 0` in `𝔇(A)` vanishes. -/
theorem res_inj (L : SLData) {v w : ℝ → ℂ} {A : Lp ℂ 2 L.measure →ₗ.[ℂ] Lp ℂ 2 L.measure}
    (hA : (A.graph : Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure)) =
      operatorGraph L (bcDomain L v w))
    {z : ℂ} {R : Lp ℂ 2 L.measure →L[ℂ] Lp ℂ 2 L.measure} (hR : IsResolventAt A z R)
    {u : ℝ → ℂ} (hD : bcDomain L v w u) (hu : IsSolution L z 0 u) : ∀ x ∈ L.I, u x = 0 := by
  have hu2 : MemLp u 2 L.measure := hD.1.1
  have hzu : MemLp (fun x => z * u x + (0 : ℝ → ℂ) x) 2 L.measure := by
    simpa using hu2.const_mul z
  obtain ⟨y, hy1, hy2⟩ := graph_mem L hA hu2 hzu hD hu
  have h0 : A y - z • (y : Lp ℂ 2 L.measure) = 0 := by
    rw [hy1, hy2, sub_eq_zero]
    ext1
    filter_upwards [hzu.coeFn_toLp, Lp.coeFn_smul z (hu2.toLp u), hu2.coeFn_toLp] with x h1 h2 h3
    rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul]; simp
  have := hR.2 y
  rw [h0, map_zero] at this
  have hy0 : hu2.toLp u = 0 := by rw [← hy1, ← this]
  have hae : u =ᵐ[L.measure] (0 : ℝ → ℂ) := by
    have := hu2.coeFn_toLp
    rw [hy0] at this
    exact this.symm.trans (Lp.coeFn_zero _ _ _)
  exact eqOn_of_ae L (sol_contOn L hu) continuousOn_const hae

/-! ### Linear combinations of solutions -/

theorem lin_sol (L : SLData) {z : ℂ} {u1 u2 : ℝ → ℂ} (h1 : IsSolution L z 0 u1)
    (h2 : IsSolution L z 0 u2) (a b : ℂ) :
    IsSolution L z 0 (fun x => a * u1 x + b * u2 x) := by
  have := solvesTau_add L (solvesTau_smul L h1 a) (solvesTau_smul L h2 b)
  unfold IsSolution
  convert this using 2 with x
  simp only [Pi.zero_apply, add_zero]; ring

theorem lin_qd (L : SLData) {z : ℂ} {u1 u2 : ℝ → ℂ} (h1 : IsSolution L z 0 u1)
    (h2 : IsSolution L z 0 u2) (a b : ℂ) :
    ∀ x ∈ L.I, quasiDeriv L (fun x => a * u1 x + b * u2 x) x =
      a * quasiDeriv L u1 x + b * quasiDeriv L u2 x := by
  intro x hx
  rw [qd_add L (solvesTau_smul L h1 a) (solvesTau_smul L h2 b) x hx,
    qd_smul L h1 a x hx, qd_smul L h2 b x hx]

theorem wr_lin (L : SLData) {z : ℂ} {u1 u2 : ℝ → ℂ} (h1 : IsSolution L z 0 u1)
    (h2 : IsSolution L z 0 u2) (a1 b1 a2 b2 : ℂ) {x : ℝ} (hx : x ∈ L.I) :
    wronskian L x (fun x => a1 * u1 x + b1 * u2 x) (fun x => a2 * u1 x + b2 * u2 x) =
      (a1 * b2 - b1 * a2) * wronskian L x u1 u2 := by
  unfold wronskian
  rw [lin_qd L h1 h2 a1 b1 x hx, lin_qd L h1 h2 a2 b2 x hx]
  ring

/-! ### Boundary Wronskians of elements of `𝔇(A)` -/

theorem wLeft_bc_zero (L : SLData) {v w : ℝ → ℂ} (H : BcHyp L v w) {f g : ℝ → ℂ}
    (hf : bcDomain L v w f) (hg : bcDomain L v w g) : wronskianLeft L f g = 0 := by
  by_cases hl : IsLimitCircleLeft L
  · obtain ⟨hv, -, f0, hf0, hne⟩ := H.1 hl
    have p := BcAux.plucker_left L hv hf0 hf.1 hg.1
    rw [hf.2.1 hl, hg.2.1 hl] at p
    have : wronskianLeft L v f0 * wronskianLeft L f g = 0 := by linear_combination p
    exact (mul_eq_zero.mp this).resolve_left hne
  · exact lp_W_zero_left L hl hf.1 hg.1

theorem wRight_bc_zero (L : SLData) {v w : ℝ → ℂ} (H : BcHyp L v w) {f g : ℝ → ℂ}
    (hf : bcDomain L v w f) (hg : bcDomain L v w g) : wronskianRight L f g = 0 := by
  by_cases hr : IsLimitCircleRight L
  · obtain ⟨hw, -, f0, hf0, hne⟩ := H.2 hr
    have p := BcAuxR.plucker_right L hw hf0 hf.1 hg.1
    rw [hf.2.2 hr, hg.2.2 hr] at p
    have : wronskianRight L w f0 * wronskianRight L f g = 0 := by linear_combination p
    exact (mul_eq_zero.mp this).resolve_left hne
  · exact lp_W_zero_right L hr hf.1 hg.1

/-- A solution agreeing with elements of `𝔇(A)` near both endpoints lies in `𝔇(A)`. -/
theorem bc_of_pieces (L : SLData) {v w : ℝ → ℂ} {z : ℂ} {u fa fb : ℝ → ℂ} {c d : ℝ}
    (hc : c ∈ L.I) (hd : d ∈ L.I) (hcd : c ≤ d) (hu : IsSolution L z 0 u)
    (ha : bcDomain L v w fa) (hb : bcDomain L v w fb)
    (hla : ∀ x ∈ L.I, x ≤ c → fa x = u x ∧ quasiDeriv L fa x = quasiDeriv L u x)
    (hlb : ∀ x ∈ L.I, d ≤ x → fb x = u x ∧ quasiDeriv L fb x = quasiDeriv L u x) :
    bcDomain L v w u := by
  have hu2 : MemLp u 2 L.measure := by
    have m1 : MemLp ((Iic c).indicator fa) 2 L.measure := ha.1.1.indicator measurableSet_Iic
    have m2 : MemLp ((Ioc c d).indicator u) 2 L.measure := memLp_Ioc L (sol_contOn L hu) hc hd hcd
    have m3 : MemLp ((Ioi d).indicator fb) 2 L.measure := hb.1.1.indicator measurableSet_Ioi
    refine ((m1.add m2).add m3).ae_eq (ae_measure_of_forall L fun x hx => ?_)
    simp only [Pi.add_apply, indicator]
    by_cases h1 : x ≤ c
    · have : ¬ (c < x) := not_lt.mpr h1
      simp [h1, this, (hla x hx h1).1, show ¬ d < x from fun h => this (lt_of_le_of_lt hcd h)]
    · push_neg at h1
      by_cases h2 : x ≤ d
      · simp [h2, h1, not_le.mpr h1, not_lt.mpr h2]
      · push_neg at h2
        simp [h2, not_le.mpr h1, not_le.mpr h2, (hlb x hx h2.le).1]
  have hU : MemLp (fun x => z * u x + (0 : ℝ → ℂ) x) 2 L.measure := by
    simpa using hu2.const_mul z
  refine ⟨⟨hu2, _, hu, hU⟩, fun hl => ?_, fun hr => ?_⟩
  · rw [← ha.2.1 hl]
    refine wLeft_congr L (((eventually_mem_left L).and (eventually_lt_left L hc.1)).mono
      fun x hx => ?_)
    obtain ⟨e1, e2⟩ := hla x hx.1 hx.2.le
    unfold wronskian; rw [e1, e2]
  · rw [← hb.2.2 hr]
    refine wRight_congr L (((eventually_mem_right L).and (eventually_gt_right L hd.2)).mono
      fun x hx => ?_)
    obtain ⟨e1, e2⟩ := hlb x hx.1 hx.2.le
    unfold wronskian; rw [e1, e2]

end RGAux

end SecRG1

section SecRG2

/-! # Lemma 9.7, part 2: one-sided integrals against `L²` functions -/

open MeasureTheory Set Filter Topology
open scoped Interval

namespace RGAux

open TeschlQM.SturmLiouville VoCAux LagAux IvpAux WeylAux SAAux

/-- Set integrals over subintervals of `I` with respect to `r dx`. -/
theorem setInt_Ioc (L : SLData) {F : ℝ → ℂ} {c x : ℝ} (hc : c ∈ L.I) (hx : x ∈ L.I)
    (hcx : c ≤ x) :
    ∫ y in Ioc c x, F y ∂L.measure = ∫ y in c..x, F y * (L.r y : ℂ) := by
  rw [← integral_indicator measurableSet_Ioc, integral_measure_eq,
    intervalIntegral.integral_of_le hcx]
  have hsub : Ioc c x ⊆ L.I := Ioc_subset_Icc_self.trans (Icc_sub_I L hc hx)
  have e : ∀ y, (L.r y : ℂ) * (Ioc c x).indicator F y = (Ioc c x).indicator
      (fun y => F y * (L.r y : ℂ)) y := by
    intro y; by_cases h : y ∈ Ioc c x
    · simp [indicator_of_mem h, mul_comm]
    · simp [indicator_of_notMem h]
  simp_rw [e]
  rw [setIntegral_indicator measurableSet_Ioc, inter_eq_right.mpr hsub]

theorem memLp_Iic (L : SLData) {u : ℝ → ℂ} (hu : ContinuousOn u L.I)
    (hsq : IsSqIntegrableNearLeft L u) {x : ℝ} (hx : x ∈ L.I) :
    MemLp ((Iic x).indicator u) 2 L.measure := by
  obtain ⟨c, hc, hm⟩ := hsq
  set S := {y : ℝ | L.a < (y : EReal) ∧ y < c} with hS
  have mS : MemLp (S.indicator u) 2 L.measure := by
    rw [memLp_indicator_iff_restrict (measSL L c), measure_restrict_eq L (measSL L c) (SL_sub L hc)]
    exact hm
  by_cases hxc : x < c
  · refine (mS.indicator (measurableSet_Iic (a := x))).ae_eq (ae_measure_of_forall L fun y hy => ?_)
    by_cases h : y ≤ x
    · have : y ∈ S := ⟨hy.1, lt_of_le_of_lt h hxc⟩
      rw [indicator_of_mem (show y ∈ Iic x from h), indicator_of_mem (show y ∈ Iic x from h),
        indicator_of_mem this]
    · rw [indicator_of_notMem (show y ∉ Iic x from h), indicator_of_notMem (show y ∉ Iic x from h)]
  · push_neg at hxc
    have m2 : MemLp ((Icc c x).indicator u) 2 L.measure := by
      rw [memLp_indicator_iff_restrict measurableSet_Icc,
        measure_restrict_eq L measurableSet_Icc (Icc_sub_I L hc hx)]
      exact memLp_of_contOn L hc hx hxc hu
    refine (mS.add m2).ae_eq (ae_measure_of_forall L fun y hy => ?_)
    simp only [Pi.add_apply]
    by_cases h1 : y < c
    · have hyS : y ∈ S := ⟨hy.1, h1⟩
      have hyx : y ∈ Iic x := (h1.le.trans hxc : y ≤ x)
      have hyC : y ∉ Icc c x := fun h => absurd h.1 (not_le.mpr h1)
      rw [indicator_of_mem hyS, indicator_of_notMem hyC, indicator_of_mem hyx, add_zero]
    · push_neg at h1
      have hyS : y ∉ S := fun h => absurd h.2 (not_lt.mpr h1)
      rw [indicator_of_notMem hyS, zero_add]
      by_cases h2 : y ≤ x
      · rw [indicator_of_mem (show y ∈ Icc c x from ⟨h1, h2⟩),
          indicator_of_mem (show y ∈ Iic x from h2)]
      · rw [indicator_of_notMem (show y ∉ Icc c x from fun h => h2 h.2),
          indicator_of_notMem (show y ∉ Iic x from h2)]

theorem memLp_Ioi (L : SLData) {u : ℝ → ℂ} (hu : ContinuousOn u L.I)
    (hsq : IsSqIntegrableNearRight L u) {x : ℝ} (hx : x ∈ L.I) :
    MemLp ((Ioi x).indicator u) 2 L.measure := by
  obtain ⟨c, hc, hm⟩ := hsq
  set S := {y : ℝ | c < y ∧ (y : EReal) < L.b} with hS
  have mS : MemLp (S.indicator u) 2 L.measure := by
    rw [memLp_indicator_iff_restrict (measSR L c), measure_restrict_eq L (measSR L c) (SR_sub L hc)]
    exact hm
  by_cases hxc : c < x
  · refine (mS.indicator (measurableSet_Ioi (a := x))).ae_eq (ae_measure_of_forall L fun y hy => ?_)
    by_cases h : x < y
    · have : y ∈ S := ⟨hxc.trans h, hy.2⟩
      rw [indicator_of_mem (show y ∈ Ioi x from h), indicator_of_mem (show y ∈ Ioi x from h),
        indicator_of_mem this]
    · rw [indicator_of_notMem (show y ∉ Ioi x from h), indicator_of_notMem (show y ∉ Ioi x from h)]
  · push_neg at hxc
    have m2 : MemLp ((Ioc x c).indicator u) 2 L.measure := memLp_Ioc L hu hx hc hxc
    refine (mS.add m2).ae_eq (ae_measure_of_forall L fun y hy => ?_)
    simp only [Pi.add_apply]
    by_cases h1 : c < y
    · have hyS : y ∈ S := ⟨h1, hy.2⟩
      have hyx : y ∈ Ioi x := (lt_of_le_of_lt hxc h1 : x < y)
      have hyC : y ∉ Ioc x c := fun h => absurd h.2 (not_le.mpr h1)
      rw [indicator_of_mem hyS, indicator_of_notMem hyC, indicator_of_mem hyx, add_zero]
    · push_neg at h1
      have hyS : y ∉ S := fun h => absurd h.1 (not_lt.mpr h1)
      rw [indicator_of_notMem hyS, zero_add]
      by_cases h2 : x < y
      · rw [indicator_of_mem (show y ∈ Ioc x c from ⟨h2, h1⟩),
          indicator_of_mem (show y ∈ Ioi x from h2)]
      · rw [indicator_of_notMem (show y ∉ Ioc x c from fun h => h2 h.1),
          indicator_of_notMem (show y ∉ Ioi x from h2)]

theorem intOn_of_memLp (L : SLData) {u g : ℝ → ℂ} {s : Set ℝ} (hs : MeasurableSet s)
    (hu : MemLp (s.indicator u) 2 L.measure) (hg : MemLp g 2 L.measure) :
    IntegrableOn (fun y => u y * g y) s L.measure := by
  have := hu.integrable_mul hg
  rw [← integrable_indicator_iff hs]
  refine this.congr (Eventually.of_forall fun y => ?_)
  by_cases h : y ∈ s
  · simp [indicator_of_mem h]
  · simp [indicator_of_notMem h]

theorem intOn_Iic (L : SLData) {u g : ℝ → ℂ} (hu : ContinuousOn u L.I)
    (hsq : IsSqIntegrableNearLeft L u) (hg : MemLp g 2 L.measure) {x : ℝ} (hx : x ∈ L.I) :
    IntegrableOn (fun y => u y * g y) (Iic x) L.measure :=
  intOn_of_memLp L measurableSet_Iic (memLp_Iic L hu hsq hx) hg

theorem intOn_Ioi (L : SLData) {u g : ℝ → ℂ} (hu : ContinuousOn u L.I)
    (hsq : IsSqIntegrableNearRight L u) (hg : MemLp g 2 L.measure) {x : ℝ} (hx : x ∈ L.I) :
    IntegrableOn (fun y => u y * g y) (Ioi x) L.measure :=
  intOn_of_memLp L measurableSet_Ioi (memLp_Ioi L hu hsq hx) hg

theorem prim_Iic (L : SLData) {u g : ℝ → ℂ} (hu : ContinuousOn u L.I)
    (hsq : IsSqIntegrableNearLeft L u) (hg : MemLp g 2 L.measure) {c x : ℝ} (hc : c ∈ L.I)
    (hx : x ∈ L.I) :
    ∫ y in Iic x, u y * g y ∂L.measure - ∫ y in Iic c, u y * g y ∂L.measure =
      ∫ y in c..x, u y * g y * (L.r y : ℂ) := by
  rcases le_total c x with hcx | hxc
  · rw [← Iic_union_Ioc_eq_Iic hcx, setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
      (intOn_Iic L hu hsq hg hc) ((intOn_Iic L hu hsq hg hx).mono_set Ioc_subset_Iic_self),
      add_sub_cancel_left, setInt_Ioc L hc hx hcx]
  · rw [← Iic_union_Ioc_eq_Iic hxc, setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
      (intOn_Iic L hu hsq hg hx) ((intOn_Iic L hu hsq hg hc).mono_set Ioc_subset_Iic_self),
      setInt_Ioc L hx hc hxc, intervalIntegral.integral_symm]
    ring

theorem prim_Ioi (L : SLData) {u g : ℝ → ℂ} (hu : ContinuousOn u L.I)
    (hsq : IsSqIntegrableNearRight L u) (hg : MemLp g 2 L.measure) {c x : ℝ} (hc : c ∈ L.I)
    (hx : x ∈ L.I) :
    ∫ y in Ioi c, u y * g y ∂L.measure - ∫ y in Ioi x, u y * g y ∂L.measure =
      ∫ y in c..x, u y * g y * (L.r y : ℂ) := by
  rcases le_total c x with hcx | hxc
  · rw [← Ioc_union_Ioi_eq_Ioi hcx, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      ((intOn_Ioi L hu hsq hg hc).mono_set Ioc_subset_Ioi_self) (intOn_Ioi L hu hsq hg hx),
      add_sub_cancel_right, setInt_Ioc L hc hx hcx]
  · rw [← Ioc_union_Ioi_eq_Ioi hxc, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      ((intOn_Ioi L hu hsq hg hx).mono_set Ioc_subset_Ioi_self) (intOn_Ioi L hu hsq hg hc),
      setInt_Ioc L hx hc hxc, intervalIntegral.integral_symm]
    ring

theorem tendsto_Iic (L : SLData) {u g : ℝ → ℂ} (hu : ContinuousOn u L.I)
    (hsq : IsSqIntegrableNearLeft L u) (hg : MemLp g 2 L.measure) :
    Tendsto (fun x => ∫ y in Iic x, u y * g y ∂L.measure) L.atLeft (𝓝 0) := by
  obtain ⟨c, hc⟩ := exists_mem_I L
  simp_rw [← integral_indicator measurableSet_Iic]
  have key := tendsto_integral_filter_of_dominated_convergence (μ := L.measure) (l := L.atLeft)
    (F := fun x => (Iic x).indicator (fun y => u y * g y)) (f := fun _ => (0 : ℂ))
    (fun y => ‖(Iic c).indicator (fun y => u y * g y) y‖)
    ((eventually_mem_left L).mono fun x hx =>
      ((integrable_indicator_iff measurableSet_Iic).mpr
        (intOn_Iic L hu hsq hg hx)).aestronglyMeasurable)
    ((eventually_lt_left L hc.1).mono fun x hx => Eventually.of_forall fun y =>
      norm_indicator_le_of_subset (Iic_subset_Iic.mpr hx.le) _ _)
    ((integrable_indicator_iff measurableSet_Iic).mpr (intOn_Iic L hu hsq hg hc)).norm
    (ae_measure_of_forall L fun y hy => tendsto_const_nhds.congr'
      ((eventually_lt_left L hy.1).mono fun x hx =>
        (indicator_of_notMem (show y ∉ Iic x from not_le.mpr hx) _).symm))
  simpa using key

theorem tendsto_Ioi (L : SLData) {u g : ℝ → ℂ} (hu : ContinuousOn u L.I)
    (hsq : IsSqIntegrableNearRight L u) (hg : MemLp g 2 L.measure) :
    Tendsto (fun x => ∫ y in Ioi x, u y * g y ∂L.measure) L.atRight (𝓝 0) := by
  obtain ⟨c, hc⟩ := exists_mem_I L
  simp_rw [← integral_indicator measurableSet_Ioi]
  have key := tendsto_integral_filter_of_dominated_convergence (μ := L.measure) (l := L.atRight)
    (F := fun x => (Ioi x).indicator (fun y => u y * g y)) (f := fun _ => (0 : ℂ))
    (fun y => ‖(Ioi c).indicator (fun y => u y * g y) y‖)
    ((eventually_mem_right L).mono fun x hx =>
      ((integrable_indicator_iff measurableSet_Ioi).mpr
        (intOn_Ioi L hu hsq hg hx)).aestronglyMeasurable)
    ((eventually_gt_right L hc.2).mono fun x hx => Eventually.of_forall fun y =>
      norm_indicator_le_of_subset (Ioi_subset_Ioi hx.le) _ _)
    ((integrable_indicator_iff measurableSet_Ioi).mpr (intOn_Ioi L hu hsq hg hc)).norm
    (ae_measure_of_forall L fun y hy => tendsto_const_nhds.congr'
      ((eventually_gt_right L hy.2).mono fun x hx =>
        (indicator_of_notMem (show y ∉ Ioi x from not_lt.mpr hx.le) _).symm))
  simpa using key

end RGAux

end SecRG2

section SecRG3

/-! # Lemma 9.7, part 3: existence of `u_a`, `u_b` with nonzero Wronskian -/

open MeasureTheory Set Filter Topology
open scoped Interval

namespace RGAux

open TeschlQM.SturmLiouville VoCAux LagAux IvpAux WeylAux SAAux

theorem ind_fun_eq (L : SLData) (u χ : ℝ → ℂ) (c d : ℝ) :
    (fun y => u y * (Ioc c d).indicator χ y * (L.r y : ℂ)) =
      (Ioc c d).indicator (fun y => u y * χ y * (L.r y : ℂ)) := by
  funext y
  by_cases h : y ∈ Ioc c d
  · simp [indicator_of_mem h]
  · simp [indicator_of_notMem h]

theorem int_split (L : SLData) {u χ : ℝ → ℂ} (hu : ContinuousOn u L.I) (hχ : ContinuousOn χ L.I)
    {c d x : ℝ} (hc : c ∈ L.I) (hd : d ∈ L.I) (hcd : c ≤ d) (hx : d ≤ x) :
    ∫ y in c..x, u y * (Ioc c d).indicator χ y * (L.r y : ℂ) =
      ∫ y in c..d, u y * (Ioc c d).indicator χ y * (L.r y : ℂ) := by
  have hi : Integrable (fun y => u y * (Ioc c d).indicator χ y * (L.r y : ℂ)) := by
    rw [ind_fun_eq, integrable_indicator_iff measurableSet_Ioc]
    exact intOn_Ioc L (hu.mul hχ) hc hd hcd
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := d) hi.intervalIntegrable
    hi.intervalIntegrable, int_tail_zero L hx, add_zero]

/-- The test functions `R (1_{(c,d]} χ)`. -/
theorem test_fn (L : SLData) {v w : ℝ → ℂ} {A : Lp ℂ 2 L.measure →ₗ.[ℂ] Lp ℂ 2 L.measure}
    (hA : (A.graph : Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure)) =
      operatorGraph L (bcDomain L v w))
    {z : ℂ} {R : Lp ℂ 2 L.measure →L[ℂ] Lp ℂ 2 L.measure} (hR : IsResolventAt A z R)
    {u1 u2 : ℝ → ℂ} (h1 : IsSolution L z 0 u1) (h2 : IsSolution L z 0 u2)
    (hW : ∀ x ∈ L.I, wronskian L x u1 u2 = 1) {c d : ℝ} (hc : c ∈ L.I) (hd : d ∈ L.I)
    (hcd : c ≤ d) {χ : ℝ → ℂ} (hχ : ContinuousOn χ L.I) :
    ∃ f : ℝ → ℂ, ∃ α β : ℂ, bcDomain L v w f ∧
      (∀ x ∈ L.I, x ≤ c → f x = α * u1 x + β * u2 x ∧
        quasiDeriv L f x = α * quasiDeriv L u1 x + β * quasiDeriv L u2 x) ∧
      (∀ x ∈ L.I, d ≤ x →
        f x = (α + ∫ y in c..d, u2 y * (Ioc c d).indicator χ y * (L.r y : ℂ)) * u1 x +
          (β - ∫ y in c..d, u1 y * (Ioc c d).indicator χ y * (L.r y : ℂ)) * u2 x ∧
        quasiDeriv L f x =
          (α + ∫ y in c..d, u2 y * (Ioc c d).indicator χ y * (L.r y : ℂ)) * quasiDeriv L u1 x +
          (β - ∫ y in c..d, u1 y * (Ioc c d).indicator χ y * (L.r y : ℂ)) * quasiDeriv L u2 x) := by
  obtain ⟨f, -, hD, hs⟩ := res_rep L hA hR (memLp_Ioc L hχ hc hd hcd)
  obtain ⟨α, β, hf⟩ := voc L z _ u1 u2 h1 h2 hW c hc f hs
  refine ⟨f, α, β, hD, fun x hx hxc => ?_, fun x hx hdx => ?_⟩
  · obtain ⟨e1, e2⟩ := hf x hx
    rw [int_zero_of_le L hxc, int_zero_of_le L hxc] at e1 e2
    exact ⟨by rw [e1]; ring, by rw [e2]; ring⟩
  · obtain ⟨e1, e2⟩ := hf x hx
    rw [int_split L (sol_contOn L h1) hχ hc hd hcd hdx,
      int_split L (sol_contOn L h2) hχ hc hd hcd hdx] at e1 e2
    exact ⟨by rw [e1]; ring, by rw [e2]; ring⟩

theorem P_gram (L : SLData) (u χ : ℝ → ℂ) {c d : ℝ} (hcd : c ≤ d) :
    ∫ y in c..d, u y * (Ioc c d).indicator (fun y => starRingEnd ℂ (χ y)) y * (L.r y : ℂ) =
      gram L c d χ u := by
  rw [intervalIntegral.integral_of_le hcd, gram]
  refine setIntegral_congr_fun measurableSet_Ioc (fun y hy => ?_)
  simp only [indicator_of_mem hy]; ring

/-- Degenerate case at `b`. -/
theorem contra_right (L : SLData) {v w : ℝ → ℂ} (H : BcHyp L v w) {z : ℂ} {u1 u2 f1 f2 : ℝ → ℂ}
    (h1 : IsSolution L z 0 u1) (h2 : IsSolution L z 0 u2)
    (hW : ∀ x ∈ L.I, wronskian L x u1 u2 = 1) {d : ℝ} (hd : d ∈ L.I)
    (hf1 : bcDomain L v w f1) (hf2 : bcDomain L v w f2) {a1 b1 a2 b2 : ℂ}
    (e1 : ∀ x ∈ L.I, d ≤ x → f1 x = a1 * u1 x + b1 * u2 x ∧
      quasiDeriv L f1 x = a1 * quasiDeriv L u1 x + b1 * quasiDeriv L u2 x)
    (e2 : ∀ x ∈ L.I, d ≤ x → f2 x = a2 * u1 x + b2 * u2 x ∧
      quasiDeriv L f2 x = a2 * quasiDeriv L u1 x + b2 * quasiDeriv L u2 x)
    (hdet : a1 * b2 - b1 * a2 ≠ 0) : False := by
  apply hdet
  rw [← wRight_bc_zero L H hf1 hf2]
  symm
  refine wronskianRight_of_eventually L (((eventually_mem_right L).and
    (eventually_gt_right L hd.2)).mono fun x hx => ?_)
  obtain ⟨p1, q1⟩ := e1 x hx.1 hx.2.le
  obtain ⟨p2, q2⟩ := e2 x hx.1 hx.2.le
  have := hW x hx.1
  unfold wronskian at this ⊢
  rw [p1, q1, p2, q2]
  linear_combination (a1 * b2 - b1 * a2) * this

/-- Degenerate case at `a`. -/
theorem contra_left (L : SLData) {v w : ℝ → ℂ} (H : BcHyp L v w) {z : ℂ} {u1 u2 f1 f2 : ℝ → ℂ}
    (h1 : IsSolution L z 0 u1) (h2 : IsSolution L z 0 u2)
    (hW : ∀ x ∈ L.I, wronskian L x u1 u2 = 1) {c : ℝ} (hc : c ∈ L.I)
    (hf1 : bcDomain L v w f1) (hf2 : bcDomain L v w f2) {a1 b1 a2 b2 : ℂ}
    (e1 : ∀ x ∈ L.I, x ≤ c → f1 x = a1 * u1 x + b1 * u2 x ∧
      quasiDeriv L f1 x = a1 * quasiDeriv L u1 x + b1 * quasiDeriv L u2 x)
    (e2 : ∀ x ∈ L.I, x ≤ c → f2 x = a2 * u1 x + b2 * u2 x ∧
      quasiDeriv L f2 x = a2 * quasiDeriv L u1 x + b2 * quasiDeriv L u2 x)
    (hdet : a1 * b2 - b1 * a2 ≠ 0) : False := by
  apply hdet
  rw [← wLeft_bc_zero L H hf1 hf2]
  symm
  refine wronskianLeft_of_eventually L (((eventually_mem_left L).and
    (eventually_lt_left L hc.1)).mono fun x hx => ?_)
  obtain ⟨p1, q1⟩ := e1 x hx.1 hx.2.le
  obtain ⟨p2, q2⟩ := e2 x hx.1 hx.2.le
  have := hW x hx.1
  unfold wronskian at this ⊢
  rw [p1, q1, p2, q2]
  linear_combination (a1 * b2 - b1 * a2) * this

/-- The conclusion of the existence part. -/
def PairGoal (L : SLData) (v w : ℝ → ℂ) (z : ℂ) : Prop :=
  ∃ ua ub fa fb : ℝ → ℂ, ∃ ca cb : ℝ, ca ∈ L.I ∧ cb ∈ L.I ∧
    IsSolution L z 0 ua ∧ IsSolution L z 0 ub ∧ bcDomain L v w fa ∧ bcDomain L v w fb ∧
    (∀ x ∈ L.I, x ≤ ca → fa x = ua x ∧ quasiDeriv L fa x = quasiDeriv L ua x) ∧
    (∀ x ∈ L.I, cb ≤ x → fb x = ub x ∧ quasiDeriv L fb x = quasiDeriv L ub x) ∧
    ∃ W₀ : ℂ, W₀ ≠ 0 ∧ ∀ x ∈ L.I, wronskian L x ub ua = W₀

/-- The generic case: a nonzero left solution and a nonzero right solution. -/
theorem finish_pair (L : SLData) {v w : ℝ → ℂ} (H : BcHyp L v w)
    {A : Lp ℂ 2 L.measure →ₗ.[ℂ] Lp ℂ 2 L.measure}
    (hA : (A.graph : Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure)) =
      operatorGraph L (bcDomain L v w))
    {z : ℂ} {R : Lp ℂ 2 L.measure →L[ℂ] Lp ℂ 2 L.measure} (hR : IsResolventAt A z R)
    {u1 u2 fa fb : ℝ → ℂ} (h1 : IsSolution L z 0 u1) (h2 : IsSolution L z 0 u2)
    (hW : ∀ x ∈ L.I, wronskian L x u1 u2 = 1) {c d : ℝ} (hc : c ∈ L.I) (hd : d ∈ L.I)
    (hcd : c < d) (ha : bcDomain L v w fa) (hb : bcDomain L v w fb) {α β α' β' : ℂ}
    (ea : ∀ x ∈ L.I, x ≤ c → fa x = α * u1 x + β * u2 x ∧
      quasiDeriv L fa x = α * quasiDeriv L u1 x + β * quasiDeriv L u2 x)
    (eb : ∀ x ∈ L.I, d ≤ x → fb x = α' * u1 x + β' * u2 x ∧
      quasiDeriv L fb x = α' * quasiDeriv L u1 x + β' * quasiDeriv L u2 x)
    (hne : ¬ (α = 0 ∧ β = 0)) (hne' : ¬ (α' = 0 ∧ β' = 0)) : PairGoal L v w z := by
  set ua : ℝ → ℂ := fun x => α * u1 x + β * u2 x with hua
  set ub : ℝ → ℂ := fun x => α' * u1 x + β' * u2 x with hub
  have hla : ∀ x ∈ L.I, x ≤ c → fa x = ua x ∧ quasiDeriv L fa x = quasiDeriv L ua x :=
    fun x hx hxc => ⟨(ea x hx hxc).1, by rw [(ea x hx hxc).2, lin_qd L h1 h2 α β x hx]⟩
  have hlb : ∀ x ∈ L.I, d ≤ x → fb x = ub x ∧ quasiDeriv L fb x = quasiDeriv L ub x :=
    fun x hx hxd => ⟨(eb x hx hxd).1, by rw [(eb x hx hxd).2, lin_qd L h1 h2 α' β' x hx]⟩
  have hWx : ∀ x ∈ L.I, wronskian L x ub ua = α' * β - β' * α := by
    intro x hx
    rw [wr_lin L h1 h2 α' β' α β hx, hW x hx, mul_one]
  by_cases h0 : α' * β - β' * α = 0
  · exfalso
    -- `ua` is a multiple of `ub`, hence lies in `𝔇(A)`
    obtain ⟨lam, hl1, hl2⟩ : ∃ lam : ℂ, α = lam * α' ∧ β = lam * β' := by
      by_cases hα' : α' = 0
      · have hβ' : β' ≠ 0 := fun h => hne' ⟨hα', h⟩
        refine ⟨β / β', ?_, by field_simp⟩
        rw [hα'] at h0 ⊢
        have : β' * α = 0 := by linear_combination -h0
        rw [mul_zero]; exact (mul_eq_zero.mp this).resolve_left hβ'
      · refine ⟨α / α', by field_simp, ?_⟩
        field_simp
        linear_combination h0
    obtain ⟨-, F, hF, -⟩ := hb.1
    have hlb' : ∀ x ∈ L.I, d ≤ x → (fun x => lam * fb x) x = ua x ∧
        quasiDeriv L (fun x => lam * fb x) x = quasiDeriv L ua x := by
      intro x hx hxd
      obtain ⟨p, q⟩ := eb x hx hxd
      refine ⟨?_, ?_⟩
      · simp only [hua, p, hl1, hl2]; ring
      · rw [qd_smul L hF lam x hx, q, lin_qd L h1 h2 α β x hx, hl1, hl2]; ring
    have hbc := bc_of_pieces L hc hd hcd.le (lin_sol L h1 h2 α β) ha (bc_smul L H lam fb hb)
      hla hlb'
    have hz := res_inj L hA hR hbc (lin_sol L h1 h2 α β)
    exact hne (indep_on_interval L h1 h2 hW hc hd hcd α β fun x hx =>
      hz x (Icc_sub_I L hc hd (Ioo_subset_Icc_self hx)))
  · exact ⟨ua, ub, fa, fb, c, d, hc, hd, lin_sol L h1 h2 α β, lin_sol L h1 h2 α' β', ha, hb,
      hla, hlb, _, h0, hWx⟩

/-- **Existence of `u_a`, `u_b`.** -/
theorem exists_pair (L : SLData) {v w : ℝ → ℂ} (H : BcHyp L v w)
    {A : Lp ℂ 2 L.measure →ₗ.[ℂ] Lp ℂ 2 L.measure}
    (hA : (A.graph : Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure)) =
      operatorGraph L (bcDomain L v w))
    {z : ℂ} {R : Lp ℂ 2 L.measure →L[ℂ] Lp ℂ 2 L.measure} (hR : IsResolventAt A z R) :
    PairGoal L v w z := by
  obtain ⟨u1, u2, h1, h2, hW⟩ := fund_system L z
  obtain ⟨c, hc⟩ := exists_mem_I L
  obtain ⟨-, d, -, hcd, -, hd⟩ := exists_Icc_subset_I L hc
  have hc1 : ContinuousOn (fun y => starRingEnd ℂ (u1 y)) L.I :=
    Complex.continuous_conj.comp_continuousOn (sol_contOn L h1)
  have hc2 : ContinuousOn (fun y => starRingEnd ℂ (u2 y)) L.I :=
    Complex.continuous_conj.comp_continuousOn (sol_contOn L h2)
  obtain ⟨f1, α1, β1, hD1, l1, r1⟩ := test_fn L hA hR h1 h2 hW hc hd hcd.le hc1
  obtain ⟨f2, α2, β2, hD2, l2, r2⟩ := test_fn L hA hR h1 h2 hW hc hd hcd.le hc2
  rw [P_gram L _ _ hcd.le, P_gram L _ _ hcd.le] at r1 r2
  have hD := gram_ne L h1 h2 hW hc hd hcd
  set G11 := gram L c d u1 u1
  set G12 := gram L c d u1 u2
  set G21 := gram L c d u2 u1
  set G22 := gram L c d u2 u2
  by_cases ha : (α1 = 0 ∧ β1 = 0) ∧ (α2 = 0 ∧ β2 = 0)
  · exfalso
    obtain ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩ := ha
    refine contra_right L H h1 h2 hW hd hD1 hD2 r1 r2 ?_
    rw [a1, b1, a2, b2]
    intro h; apply hD; linear_combination h
  by_cases hb : (α1 + G12 = 0 ∧ β1 - G11 = 0) ∧ (α2 + G22 = 0 ∧ β2 - G21 = 0)
  · exfalso
    obtain ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩ := hb
    refine contra_left L H h1 h2 hW hc hD1 hD2 l1 l2 ?_
    have e1 : α1 = -G12 := by linear_combination a1
    have e2 : β1 = G11 := by linear_combination b1
    have e3 : α2 = -G22 := by linear_combination a2
    have e4 : β2 = G21 := by linear_combination b2
    rw [e1, e2, e3, e4]
    intro h; apply hD; linear_combination h
  have hL : ∃ f : ℝ → ℂ, ∃ α β : ℂ, bcDomain L v w f ∧ ¬ (α = 0 ∧ β = 0) ∧
      ∀ x ∈ L.I, x ≤ c → f x = α * u1 x + β * u2 x ∧
        quasiDeriv L f x = α * quasiDeriv L u1 x + β * quasiDeriv L u2 x := by
    by_cases h : α1 = 0 ∧ β1 = 0
    · exact ⟨f2, α2, β2, hD2, fun h' => ha ⟨h, h'⟩, l2⟩
    · exact ⟨f1, α1, β1, hD1, h, l1⟩
  have hR' : ∃ f : ℝ → ℂ, ∃ α β : ℂ, bcDomain L v w f ∧ ¬ (α = 0 ∧ β = 0) ∧
      ∀ x ∈ L.I, d ≤ x → f x = α * u1 x + β * u2 x ∧
        quasiDeriv L f x = α * quasiDeriv L u1 x + β * quasiDeriv L u2 x := by
    by_cases h : α1 + G12 = 0 ∧ β1 - G11 = 0
    · exact ⟨f2, _, _, hD2, fun h' => hb ⟨h, h'⟩, r2⟩
    · exact ⟨f1, _, _, hD1, h, r1⟩
  obtain ⟨fa, α, β, hfa, hne, ea⟩ := hL
  obtain ⟨fb, α', β', hfb, hne', eb⟩ := hR'
  exact finish_pair L H hA hR h1 h2 hW hc hd hcd hfa hfb ea eb hne hne'

end RGAux

end SecRG3

section SecRG4

/-! # Lemma 9.7, part 4: the Green function representation of the resolvent -/

open MeasureTheory Set Filter Topology
open scoped Interval

namespace RGAux

open TeschlQM.SturmLiouville VoCAux LagAux IvpAux WeylAux SAAux

theorem sqL_of (L : SLData) {u f : ℝ → ℂ} {c : ℝ} (hc : c ∈ L.I) (hf : MemLp f 2 L.measure)
    (e : ∀ x ∈ L.I, x ≤ c → f x = u x) : IsSqIntegrableNearLeft L u := by
  refine ⟨c, hc, ?_⟩
  rw [← measure_restrict_eq L (measSL L c) (SL_sub L hc)]
  refine (hf.restrict _).ae_eq ((ae_restrict_iff' (measSL L c)).mpr
    (ae_measure_of_forall L fun x hx hxS => e x hx hxS.2.le))

theorem sqR_of (L : SLData) {u f : ℝ → ℂ} {c : ℝ} (hc : c ∈ L.I) (hf : MemLp f 2 L.measure)
    (e : ∀ x ∈ L.I, c ≤ x → f x = u x) : IsSqIntegrableNearRight L u := by
  refine ⟨c, hc, ?_⟩
  rw [← measure_restrict_eq L (measSR L c) (SR_sub L hc)]
  refine (hf.restrict _).ae_eq ((ae_restrict_iff' (measSR L c)).mpr
    (ae_measure_of_forall L fun x hx hxS => e x hx hxS.1.le))

theorem smul_sol (L : SLData) {z : ℂ} {u : ℝ → ℂ} (hu : IsSolution L z 0 u) (a : ℂ) :
    IsSolution L z 0 (fun x => a * u x) := by
  have := solvesTau_smul L hu a
  unfold IsSolution
  convert this using 2 with x
  simp only [Pi.zero_apply, add_zero]; ring

/-- Splitting the Green kernel. -/
theorem kernel_split (ua ub g : ℝ → ℂ) (W₀ x : ℝ) (W : ℂ) :
    (fun y => (if y ≤ x then ub x * ua y else ua x * ub y) / W * g y) =
      fun y => (Iic x).indicator (fun y => ub x / W * (ua y * g y)) y +
        (Ioi x).indicator (fun y => ua x / W * (ub y * g y)) y := by
  funext y
  by_cases h : y ≤ x
  · have h' : y ∉ Ioi x := not_lt.mpr h
    rw [if_pos h, indicator_of_mem (show y ∈ Iic x from h), indicator_of_notMem h']
    ring
  · have h' : y ∈ Ioi x := not_le.mp h
    rw [if_neg h, indicator_of_notMem (show y ∉ Iic x from h), indicator_of_mem h']
    ring

/-- **Green formula.** -/
theorem green_formula (L : SLData) {v w : ℝ → ℂ} (H : BcHyp L v w)
    {A : Lp ℂ 2 L.measure →ₗ.[ℂ] Lp ℂ 2 L.measure}
    (hA : (A.graph : Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure)) =
      operatorGraph L (bcDomain L v w))
    {z : ℂ} {R : Lp ℂ 2 L.measure →L[ℂ] Lp ℂ 2 L.measure} (hR : IsResolventAt A z R)
    {ua ub fa fb : ℝ → ℂ} {ca cb : ℝ} (hca : ca ∈ L.I) (hcb : cb ∈ L.I)
    (hua : IsSolution L z 0 ua) (hub : IsSolution L z 0 ub) (ha : bcDomain L v w fa)
    (hb : bcDomain L v w fb)
    (ea : ∀ x ∈ L.I, x ≤ ca → fa x = ua x ∧ quasiDeriv L fa x = quasiDeriv L ua x)
    (eb : ∀ x ∈ L.I, cb ≤ x → fb x = ub x ∧ quasiDeriv L fb x = quasiDeriv L ub x)
    {W₀ : ℂ} (hW0 : W₀ ≠ 0) (hWx : ∀ x ∈ L.I, wronskian L x ub ua = W₀)
    (g : Lp ℂ 2 L.measure) :
    (∀ᵐ x ∂L.measure, Integrable
      (fun y => (if y ≤ x then ub x * ua y else ua x * ub y) / W₀ * g y) L.measure) ∧
    (R g : ℝ → ℂ) =ᵐ[L.measure]
      fun x => ∫ y, (if y ≤ x then ub x * ua y else ua x * ub y) / W₀ * g y ∂L.measure := by
  have hg : MemLp (g : ℝ → ℂ) 2 L.measure := Lp.memLp g
  have sqa : IsSqIntegrableNearLeft L ua := sqL_of L hca ha.1.1 fun x hx h => (ea x hx h).1
  have sqb : IsSqIntegrableNearRight L ub := sqR_of L hcb hb.1.1 fun x hx h => (eb x hx h).1
  have cua := sol_contOn L hua
  have cub := sol_contOn L hub
  -- integrability of the kernel
  have hint : ∀ x ∈ L.I, Integrable
      (fun y => (if y ≤ x then ub x * ua y else ua x * ub y) / W₀ * g y) L.measure := by
    intro x hx
    rw [kernel_split ua ub g x x W₀]
    exact ((integrable_indicator_iff measurableSet_Iic).mpr
      ((intOn_Iic L cua sqa hg hx).const_mul _)).add
      ((integrable_indicator_iff measurableSet_Ioi).mpr ((intOn_Ioi L cub sqb hg hx).const_mul _))
  -- the value of the kernel integral
  have hval : ∀ x ∈ L.I,
      ∫ y, (if y ≤ x then ub x * ua y else ua x * ub y) / W₀ * g y ∂L.measure =
        ub x / W₀ * ∫ y in Iic x, ua y * g y ∂L.measure +
          ua x / W₀ * ∫ y in Ioi x, ub y * g y ∂L.measure := by
    intro x hx
    rw [kernel_split ua ub g x x W₀, integral_add
      ((integrable_indicator_iff measurableSet_Iic).mpr ((intOn_Iic L cua sqa hg hx).const_mul _))
      ((integrable_indicator_iff measurableSet_Ioi).mpr ((intOn_Ioi L cub sqb hg hx).const_mul _)),
      integral_indicator measurableSet_Iic, integral_indicator measurableSet_Ioi,
      integral_const_mul, integral_const_mul]
  refine ⟨ae_measure_of_forall L hint, ?_⟩
  -- the resolvent
  obtain ⟨f, hRf, hD, hs⟩ := res_rep L hA hR hg
  rw [Lp.toLp_coeFn g hg] at hRf
  refine hRf.trans (ae_measure_of_forall L fun x hx => ?_)
  show f x = ∫ y, (if y ≤ x then ub x * ua y else ua x * ub y) / W₀ * g y ∂L.measure
  rw [hval x hx]
  revert x
  -- variation of constants with the system `u_b`, `u_a / W₀`
  set u₂ : ℝ → ℂ := fun x => W₀⁻¹ * ua x with hu₂
  have h₂ : IsSolution L z 0 u₂ := smul_sol L hua W₀⁻¹
  have qd₂ : ∀ x ∈ L.I, quasiDeriv L u₂ x = W₀⁻¹ * quasiDeriv L ua x := qd_smul L hua W₀⁻¹
  have hW1 : ∀ x ∈ L.I, wronskian L x ub u₂ = 1 := by
    intro x hx
    have := hWx x hx
    unfold wronskian at this ⊢
    rw [qd₂ x hx]
    simp only [hu₂]
    field_simp
    linear_combination this
  obtain ⟨c, hc⟩ := exists_mem_I L
  obtain ⟨α, β, hf⟩ := voc L z _ ub u₂ hub h₂ hW1 c hc f hs
  set Φ : ℝ → ℂ := fun x => ∫ y in Iic x, ua y * g y ∂L.measure with hΦ
  set Ψ : ℝ → ℂ := fun x => ∫ y in Ioi x, ub y * g y ∂L.measure with hΨ
  have eIa : ∀ x ∈ L.I, ∫ y in c..x, u₂ y * g y * (L.r y : ℂ) = W₀⁻¹ * (Φ x - Φ c) := by
    intro x hx
    rw [prim_Iic L cua sqa hg hc hx, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp only [hu₂]; ring
  have eIb : ∀ x ∈ L.I, ∫ y in c..x, ub y * g y * (L.r y : ℂ) = Ψ c - Ψ x := fun x hx =>
    (prim_Ioi L cub sqb hg hc hx).symm
  -- the constant `α`
  have hα : α = W₀⁻¹ * Φ c := by
    have t1 : Tendsto (fun x => -(α + W₀⁻¹ * (Φ x - Φ c)) * W₀) L.atLeft (𝓝 0) := by
      have := BcAux.tendsto_W L hD.1 ha.1
      rw [wLeft_bc_zero L H ha hD] at this
      refine this.congr' (((eventually_mem_left L).and (eventually_lt_left L hca.1)).mono
        fun x hx => ?_)
      obtain ⟨p, q⟩ := ea x hx.1 hx.2.le
      obtain ⟨e1, e2⟩ := hf x hx.1
      have hw := hWx x hx.1
      unfold wronskian at hw ⊢
      rw [p, q, e1, e2, qd₂ x hx.1, eIa x hx.1, eIb x hx.1]
      simp only [hu₂]
      linear_combination (-(α + W₀⁻¹ * (Φ x - Φ c))) * hw
    have t2 : Tendsto (fun x => -(α + W₀⁻¹ * (Φ x - Φ c)) * W₀) L.atLeft
        (𝓝 (-(α + W₀⁻¹ * (0 - Φ c)) * W₀)) :=
      ((((tendsto_Iic L cua sqa hg).sub tendsto_const_nhds).const_mul W₀⁻¹).const_add α).neg.mul
        tendsto_const_nhds
    have := tendsto_nhds_unique t2 t1
    have : α + W₀⁻¹ * (0 - Φ c) = 0 := by
      rcases mul_eq_zero.mp this with h | h
      · exact neg_eq_zero.mp h
      · exact absurd h hW0
    linear_combination this
  -- the constant `β`
  have hβ : β = Ψ c := by
    have t1 : Tendsto (fun x => β - (Ψ c - Ψ x)) L.atRight (𝓝 0) := by
      have := tendsto_W_right L hD.1 hb.1
      rw [wRight_bc_zero L H hb hD] at this
      refine this.congr' (((eventually_mem_right L).and (eventually_gt_right L hcb.2)).mono
        fun x hx => ?_)
      obtain ⟨p, q⟩ := eb x hx.1 hx.2.le
      obtain ⟨e1, e2⟩ := hf x hx.1
      have hw := hWx x hx.1
      unfold wronskian at hw ⊢
      rw [p, q, e1, e2, qd₂ x hx.1, eIa x hx.1, eIb x hx.1]
      simp only [hu₂]
      field_simp
      linear_combination (β - (Ψ c - Ψ x)) * hw
    have t2 : Tendsto (fun x => β - (Ψ c - Ψ x)) L.atRight (𝓝 (β - (Ψ c - 0))) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.sub (tendsto_Ioi L cub sqb hg))
    have := tendsto_nhds_unique t2 t1
    linear_combination this
  intro x hx
  obtain ⟨e1, -⟩ := hf x hx
  rw [e1, eIa x hx, eIb x hx, hα, hβ]
  simp only [hu₂, hΦ, hΨ]
  field_simp
  ring

end RGAux

end SecRG4

section SecRG5

/-! # Teschl, Lemma 9.7 -/

open MeasureTheory Set Filter Topology

namespace RGAux

open TeschlQM.SturmLiouville VoCAux LagAux IvpAux WeylAux SAAux

/-- **Teschl, Lemma 9.7**, with the exact statement of the Prove2Me target
`TeschlQM.SturmLiouville.resolvent_green`. -/
theorem resolvent_green (L : SLData) (v w : ℝ → ℂ)
    (hv : IsLimitCircleLeft L → InMaxDomain L v ∧
      wronskianLeft L (fun x => starRingEnd ℂ (v x)) v = 0 ∧
      ∃ f : ℝ → ℂ, InMaxDomain L f ∧ wronskianLeft L v f ≠ 0)
    (hw : IsLimitCircleRight L → InMaxDomain L w ∧
      wronskianRight L (fun x => starRingEnd ℂ (w x)) w = 0 ∧
      ∃ f : ℝ → ℂ, InMaxDomain L f ∧ wronskianRight L w f ≠ 0)
    (A : Lp ℂ 2 L.measure →ₗ.[ℂ] Lp ℂ 2 L.measure)
    (hA : (A.graph : Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure)) =
      operatorGraph L (bcDomain L v w))
    (z : ℂ) (R : Lp ℂ 2 L.measure →L[ℂ] Lp ℂ 2 L.measure) (hR : IsResolventAt A z R) :
    ∃ ua ub : ℝ → ℂ,
      IsSolution L z 0 ua ∧ IsSqIntegrableNearLeft L ua ∧
        (IsLimitCircleLeft L → Tendsto (fun x => wronskian L x v ua) L.atLeft (𝓝 0)) ∧
      IsSolution L z 0 ub ∧ IsSqIntegrableNearRight L ub ∧
        (IsLimitCircleRight L → Tendsto (fun x => wronskian L x w ub) L.atRight (𝓝 0)) ∧
      ∃ W₀ : ℂ, W₀ ≠ 0 ∧ (∀ x ∈ L.I, wronskian L x ub ua = W₀) ∧
        ∀ g : Lp ℂ 2 L.measure,
          (∀ᵐ x ∂L.measure, Integrable
            (fun y => (if y ≤ x then ub x * ua y else ua x * ub y) / W₀ * g y) L.measure) ∧
          (R g : ℝ → ℂ) =ᵐ[L.measure]
            fun x => ∫ y, (if y ≤ x then ub x * ua y else ua x * ub y) / W₀ * g y ∂L.measure := by
  have H : BcHyp L v w := ⟨hv, hw⟩
  obtain ⟨ua, ub, fa, fb, ca, cb, hca, hcb, hua, hub, ha, hb, ea, eb, W₀, hW0, hWx⟩ :=
    exists_pair L H hA hR
  refine ⟨ua, ub, hua, sqL_of L hca ha.1.1 fun x hx h => (ea x hx h).1, fun hl => ?_,
    hub, sqR_of L hcb hb.1.1 fun x hx h => (eb x hx h).1, fun hr => ?_, W₀, hW0, hWx,
    green_formula L H hA hR hca hcb hua hub ha hb ea eb hW0 hWx⟩
  · have := BcAux.tendsto_W L ha.1 (hv hl).1
    rw [ha.2.1 hl] at this
    refine this.congr' (((eventually_mem_left L).and (eventually_lt_left L hca.1)).mono
      fun x hx => ?_)
    obtain ⟨p, q⟩ := ea x hx.1 hx.2.le
    unfold wronskian; rw [p, q]
  · have := tendsto_W_right L hb.1 (hw hr).1
    rw [hb.2.2 hr] at this
    refine this.congr' (((eventually_mem_right L).and (eventually_gt_right L hcb.2)).mono
      fun x hx => ?_)
    obtain ⟨p, q⟩ := eb x hx.1 hx.2.le
    unfold wronskian; rw [p, q]

end RGAux

end SecRG5

open TeschlQM.SturmLiouville MeasureTheory Filter Topology

theorem solution (L : SLData) (v w : ℝ → ℂ)
    (hv : IsLimitCircleLeft L → InMaxDomain L v ∧
      wronskianLeft L (fun x => starRingEnd ℂ (v x)) v = 0 ∧
      ∃ f : ℝ → ℂ, InMaxDomain L f ∧ wronskianLeft L v f ≠ 0)
    (hw : IsLimitCircleRight L → InMaxDomain L w ∧
      wronskianRight L (fun x => starRingEnd ℂ (w x)) w = 0 ∧
      ∃ f : ℝ → ℂ, InMaxDomain L f ∧ wronskianRight L w f ≠ 0)
    (A : Lp ℂ 2 L.measure →ₗ.[ℂ] Lp ℂ 2 L.measure)
    (hA : (A.graph : Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure)) =
      operatorGraph L (bcDomain L v w))
    (z : ℂ) (R : Lp ℂ 2 L.measure →L[ℂ] Lp ℂ 2 L.measure) (hR : IsResolventAt A z R) :
    ∃ ua ub : ℝ → ℂ,
      IsSolution L z 0 ua ∧ IsSqIntegrableNearLeft L ua ∧
        (IsLimitCircleLeft L → Tendsto (fun x => wronskian L x v ua) L.atLeft (𝓝 0)) ∧
      IsSolution L z 0 ub ∧ IsSqIntegrableNearRight L ub ∧
        (IsLimitCircleRight L → Tendsto (fun x => wronskian L x w ub) L.atRight (𝓝 0)) ∧
      ∃ W₀ : ℂ, W₀ ≠ 0 ∧ (∀ x ∈ L.I, wronskian L x ub ua = W₀) ∧
        ∀ g : Lp ℂ 2 L.measure,
          (∀ᵐ x ∂L.measure, Integrable
            (fun y => (if y ≤ x then ub x * ua y else ua x * ub y) / W₀ * g y) L.measure) ∧
          (R g : ℝ → ℂ) =ᵐ[L.measure]
            fun x => ∫ y, (if y ≤ x then ub x * ua y else ua x * ub y) / W₀ * g y ∂L.measure :=
  RGAux.resolvent_green L v w hv hw A hA z R hR

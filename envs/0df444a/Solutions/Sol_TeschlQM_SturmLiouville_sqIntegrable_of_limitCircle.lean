-- Prove2me | solution 1 for TeschlQM.SturmLiouville.sqIntegrable_of_limitCircle
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-05T16:14:54.127233+00:00
-- url     : https://prove2.me/submissions/e94679ce-eb41-4034-8692-360e1128241c

import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_maxDomain
import Definitions.Def_TeschlQM_SturmLiouville_wronskian
import Definitions.Def_TeschlQM_SturmLiouville_SolvesTau
import Definitions.Def_TeschlQM_SturmLiouville_IsSqIntegrableNear
import Definitions.Def_TeschlQM_SturmLiouville_IsLimitCircle

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
  Complex.ofRealCLM.locallyIntegrableOn_comp hf

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
    (i1.add i2).congr_fun (fun s _ => by simp only [Pi.add_apply]; ring) (measSL L c3)
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
    (i1.add i2).congr_fun (fun s _ => by simp only [Pi.add_apply]; ring) (measSR L c3)
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


open MeasureTheory Set Filter Topology
open scoped Interval

namespace WeylLP

open TeschlQM.SturmLiouville VoCAux LagAux IvpAux WeylAux

/-- `r h` is locally integrable for a solution of `(τ − z) G = h`. -/
theorem rh_loc (L : SLData) {z : ℂ} {h G : ℝ → ℂ} (hG : IsSolution L z h G) :
    LocallyIntegrableOn (fun t => (L.r t : ℂ) * h t) L.I := by
  have hc := sol_contOn L hG
  obtain ⟨-, hl, -⟩ := hG
  have h1 : LocallyIntegrableOn (fun t => (L.q t : ℂ) * G t) L.I :=
    (q_loc L).mul_continuousOn hc (I_lc L)
  have h2 : LocallyIntegrableOn (fun t => (L.r t : ℂ) * (z * G t)) L.I :=
    (r_loc' L).mul_continuousOn (continuousOn_const.mul hc) (I_lc L)
  have e : (fun t => (L.r t : ℂ) * h t) = fun t =>
      ((L.q t : ℂ) * G t - (L.r t : ℂ) * (z * G t)) -
        ((L.q t : ℂ) * G t - (L.r t : ℂ) * (z * G t + h t)) := by
    funext t; ring
  rw [e]
  exact (h1.sub h2).sub hl

/-- Integrability of `r · Im(conj(u) · h)` on compact subintervals. -/
theorem int_im (L : SLData) {z : ℂ} {h G u : ℝ → ℂ} (hG : IsSolution L z h G)
    (hu : ContinuousOn u L.I) {c y : ℝ} (hc : c ∈ L.I) (hy : y ∈ L.I) :
    IntegrableOn (fun t => L.r t * (starRingEnd ℂ (u t) * h t).im) (Ι c y) := by
  have hrh : IntegrableOn (fun t => (L.r t : ℂ) * h t) (uIcc c y) :=
    (rh_loc L hG).integrableOn_compact_subset (uIcc_subset_I L hc hy) isCompact_uIcc
  have hcu : ContinuousOn (fun t => starRingEnd ℂ (u t)) (uIcc c y) :=
    (Complex.continuous_conj.comp_continuousOn hu).mono (uIcc_subset_I L hc hy)
  have h3 : IntegrableOn (fun t => starRingEnd ℂ (u t) * ((L.r t : ℂ) * h t)) (uIcc c y) :=
    hrh.continuousOn_mul hcu isCompact_uIcc
  have h4 := (h3.mono_set uIoc_subset_uIcc).im
  refine IntegrableOn.congr_fun h4 (fun t _ => ?_) measurableSet_uIoc
  show ((starRingEnd ℂ) (u t) * ((L.r t : ℂ) * h t)).im = _
  rw [mul_left_comm, Complex.im_ofReal_mul]

theorem int_r_norm_sq (L : SLData) {u : ℝ → ℂ} (hu : ContinuousOn u L.I) {c y : ℝ}
    (hc : c ∈ L.I) (hy : y ∈ L.I) :
    IntegrableOn (fun t => L.r t * ‖u t‖ ^ 2) (Ι c y) :=
  int_r_mul L (φ := fun t => ‖u t‖ ^ 2) (hu.norm.pow 2) hc hy

theorem Nrm_nonneg (L : SLData) (u : ℝ → ℂ) {y c : ℝ} (hy : y ∈ L.I) (hc : c ∈ L.I) :
    0 ≤ Nrm L u y c :=
  setIntegral_nonneg measurableSet_uIoc fun t ht =>
    mul_nonneg (r_nonneg_of_mem L (uIoc_sub_I L hy hc ht)) (sq_nonneg _)

/-- The side condition: `z = s i` with `s = 1` on the left of `c`, `s = −1` on the right. -/
def Side (s c y : ℝ) : Prop := (s = 1 ∧ y < c) ∨ (s = -1 ∧ c < y)

theorem side_abs {s c y : ℝ} (h : Side s c y) : |s| = 1 := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

/-- The energy identity on one side of `c`. -/
theorem energy_side (L : SLData) {s : ℝ} {h G : ℝ → ℂ} (hG : IsSolution L (s * Complex.I) h G)
    {c y : ℝ} (hc : c ∈ L.I) (hy : y ∈ L.I) (hs : Side s c y) :
    imW L G y - imW L G c =
      ∫ t in Ι y c, L.r t * (‖G t‖ ^ 2 + s * (starRingEnd ℂ (G t) * h t).im) := by
  rw [energy L hG hc hy]
  have him : ((s : ℂ) * Complex.I).im = s := by simp
  rw [him]
  rcases hs with ⟨rfl, hyc⟩ | ⟨rfl, hcy⟩
  · rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hyc.le,
      uIoc_of_le hyc.le]
    simp
  · rw [intervalIntegral.integral_of_le hcy.le, uIoc_of_ge hcy.le, ← integral_neg]
    congr 1; funext t; ring

/-- The basic `L²` estimate: if `(τ − s i) G = h`, `G(c) = 0` and `Im(G* pG')(y) ≤ 0`, then the
mass of `G` between `y` and `c` is bounded by that of `h`. -/
theorem mass_le (L : SLData) {s : ℝ} {h G : ℝ → ℂ} (hG : IsSolution L (s * Complex.I) h G)
    {c y : ℝ} (hc : c ∈ L.I) (hy : y ∈ L.I) (hs : Side s c y) (hGc : G c = 0)
    (hW : imW L G y ≤ 0) (hh : IntegrableOn (fun t => L.r t * ‖h t‖ ^ 2) (Ι y c)) :
    Nrm L G y c ≤ Nrm L h y c := by
  have hE := energy_side L hG hc hy hs
  have hWc : imW L G c = 0 := by simp [imW, hGc]
  rw [hWc, sub_zero] at hE
  have hGc' := sol_contOn L hG
  have i1 : IntegrableOn (fun t => L.r t * ‖G t‖ ^ 2) (Ι y c) := int_r_norm_sq L hGc' hy hc
  have i2 := int_im L hG hGc' hy hc
  have i3 : IntegrableOn (fun t => L.r t * (‖G t‖ ^ 2 + s * (starRingEnd ℂ (G t) * h t).im))
      (Ι y c) := by
    refine IntegrableOn.congr_fun (i1.add (i2.const_mul s)) (fun t _ => ?_) measurableSet_uIoc
    simp only [Pi.add_apply]; ring
  have i4 : IntegrableOn (fun t => L.r t * ((1 / 2) * ‖G t‖ ^ 2 - (1 / 2) * ‖h t‖ ^ 2))
      (Ι y c) := by
    refine IntegrableOn.congr_fun ((i1.const_mul (1 / 2)).sub (hh.const_mul (1 / 2))) (fun t _ => ?_)
      measurableSet_uIoc
    simp only [Pi.sub_apply]; ring
  have hmono : ∫ t in Ι y c, L.r t * ((1 / 2) * ‖G t‖ ^ 2 - (1 / 2) * ‖h t‖ ^ 2) ≤
      ∫ t in Ι y c, L.r t * (‖G t‖ ^ 2 + s * (starRingEnd ℂ (G t) * h t).im) := by
    refine setIntegral_mono_on i4 i3 measurableSet_uIoc fun t ht => ?_
    have hr := r_nonneg_of_mem L (uIoc_sub_I L hy hc ht)
    refine mul_le_mul_of_nonneg_left ?_ hr
    have habs : |s * (starRingEnd ℂ (G t) * h t).im| ≤ ‖G t‖ * ‖h t‖ := by
      rw [abs_mul, side_abs hs, one_mul]
      calc |(starRingEnd ℂ (G t) * h t).im| ≤ ‖starRingEnd ℂ (G t) * h t‖ :=
            Complex.abs_im_le_norm _
        _ = ‖G t‖ * ‖h t‖ := by rw [norm_mul, Complex.norm_conj]
    have := neg_abs_le (s * (starRingEnd ℂ (G t) * h t).im)
    nlinarith [sq_nonneg (‖G t‖ - ‖h t‖)]
  have e4 : ∫ t in Ι y c, L.r t * ((1 / 2) * ‖G t‖ ^ 2 - (1 / 2) * ‖h t‖ ^ 2) =
      (1 / 2) * Nrm L G y c - (1 / 2) * Nrm L h y c := by
    unfold Nrm
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (i1.const_mul _)
      (hh.const_mul _)]
    congr 1; funext t; ring
  linarith

end WeylLP


open MeasureTheory Set Filter Topology
open scoped Interval

namespace WeylLP

open TeschlQM.SturmLiouville VoCAux LagAux IvpAux WeylAux

theorem isSolution_comb (L : SLData) {z : ℂ} {f1 f2 : ℝ → ℂ} (h1 : IsSolution L z 0 f1)
    (h2 : IsSolution L z 0 f2) (b : ℂ) :
    IsSolution L z 0 (fun x => f1 x + b * f2 x) ∧
      ∀ x ∈ L.I, quasiDeriv L (fun x => f1 x + b * f2 x) x =
        quasiDeriv L f1 x + b * quasiDeriv L f2 x := by
  obtain ⟨hs, hq⟩ := isSolution_lin L h1 h2 1 b
  have e1 : (fun x => (1 : ℂ) * f1 x + b * f2 x) = fun x => f1 x + b * f2 x := by
    funext x; ring
  have e2 : (fun x => (1 : ℂ) * (0 : ℝ → ℂ) x + b * (0 : ℝ → ℂ) x) = 0 := by
    funext x; simp
  rw [e1, e2] at hs
  rw [e1] at hq
  exact ⟨hs, fun x hx => by rw [hq x hx]; ring⟩

theorem side_total {s c y1 y2 : ℝ} (h1 : Side s c y1) (h2 : Side s c y2) :
    Ι y1 c ⊆ Ι y2 c ∨ Ι y2 c ⊆ Ι y1 c := by
  rcases h1 with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;> rcases h2 with ⟨h, h2⟩ | ⟨h, h2⟩ <;>
    try norm_num at h
  · rw [uIoc_of_le h1.le, uIoc_of_le h2.le]
    rcases le_total y1 y2 with h | h
    · exact Or.inr (Ioc_subset_Ioc_left h)
    · exact Or.inl (Ioc_subset_Ioc_left h)
  · rw [uIoc_of_ge h1.le, uIoc_of_ge h2.le]
    rcases le_total y1 y2 with h | h
    · exact Or.inl (Ioc_subset_Ioc_right h)
    · exact Or.inr (Ioc_subset_Ioc_right h)

theorem Nrm_mono (L : SLData) {u : ℝ → ℂ} (hu : ContinuousOn u L.I) {c y1 y2 : ℝ}
    (hc : c ∈ L.I) (hy2 : y2 ∈ L.I) (hsub : Ι y1 c ⊆ Ι y2 c) :
    Nrm L u y1 c ≤ Nrm L u y2 c :=
  setIntegral_mono_set (int_r_norm_sq L hu hy2 hc)
    ((ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun t ht =>
      mul_nonneg (r_nonneg_of_mem L (uIoc_sub_I L hy2 hc ht)) (sq_nonneg _)))
    (Eventually.of_forall hsub)

theorem exists_side (L : SLData) {s c : ℝ} (hc : c ∈ L.I) (hs : s = 1 ∨ s = -1) :
    ∃ y ∈ L.I, Side s c y := by
  obtain ⟨a, b, hac, hcb, ha, hb⟩ := exists_Icc_subset_I L hc
  rcases hs with rfl | rfl
  · exact ⟨a, ha, Or.inl ⟨rfl, hac⟩⟩
  · exact ⟨b, hb, Or.inr ⟨rfl, hcb⟩⟩

/-- The mass of a nontrivial solution on a nondegenerate interval is positive. -/
theorem Nrm_pos (L : SLData) {z : ℂ} {θ φ : ℝ → ℂ} (hθ : IsSolution L z 0 θ)
    (hφ : IsSolution L z 0 φ) (hW : ∀ x ∈ L.I, wronskian L x θ φ = 1) {c y : ℝ}
    (hc : c ∈ L.I) (hy : y ∈ L.I) (hyc : y ≠ c) : 0 < Nrm L φ y c := by
  have h0 := Nrm_nonneg L φ hy hc
  by_contra hneg
  have hN : Nrm L φ y c = 0 := le_antisymm (not_lt.mp hneg) h0
  have hlo : min y c ∈ L.I := by rcases le_total y c with h | h <;> simp [h, hy, hc]
  have hhi : max y c ∈ L.I := by rcases le_total y c with h | h <;> simp [h, hy, hc]
  have hlt : min y c < max y c := by
    rcases lt_or_gt_of_ne hyc with h | h <;> simp [h, h.le]
  have hint : ∫ x in Ioc (min y c) (max y c),
      starRingEnd ℂ (φ x) * φ x * (L.r x : ℂ) = 0 := by
    have e : (fun x => starRingEnd ℂ (φ x) * φ x * (L.r x : ℂ)) =
        fun x => ((L.r x * ‖φ x‖ ^ 2 : ℝ) : ℂ) := by
      funext x; rw [Complex.conj_mul']; push_cast; ring
    rw [e, integral_complex_ofReal]
    have : ∫ x in Ioc (min y c) (max y c), L.r x * ‖φ x‖ ^ 2 = Nrm L φ y c := rfl
    rw [this, hN]; simp
  have hz := zero_of_gram L (sol_contOn L hφ) hlo hhi hlt hint
  have := indep_on_interval L hθ hφ hW hlo hhi hlt 0 1 (fun x hx => by simp [hz x hx])
  exact one_ne_zero this.2

/-- Weyl's nested-disc construction: a solution of `(τ − s i) ψ = 0` whose mass on the
`s`-side of `c` is bounded, with `Im(ψ* pψ') ≤ 0` there. -/
theorem weyl_solution (L : SLData) {s c : ℝ} (hc : c ∈ L.I) (hs : s = 1 ∨ s = -1) :
    ∃ ψ φ : ℝ → ℂ, IsSolution L (s * Complex.I) 0 ψ ∧ IsSolution L (s * Complex.I) 0 φ ∧
      (∀ x ∈ L.I, wronskian L x ψ φ = 1) ∧ ψ c = 1 ∧ φ c = 0 ∧
      (∀ y ∈ L.I, Side s c y → imW L ψ y ≤ 0) ∧
      ∃ M, ∀ y ∈ L.I, Side s c y → Nrm L ψ y c ≤ M := by
  obtain ⟨F1, hF1, -, -⟩ := IvpAux.ivp L 0 (zero_loc L) c hc 1 0
  obtain ⟨F2, hF2, -, -⟩ := IvpAux.ivp L 0 (zero_loc L) c hc 0 1
  obtain ⟨θ, hθ, hθc, hθ1c⟩ : ∃ θ, IsSolution L (s * Complex.I) 0 θ ∧ θ c = 1 ∧
      quasiDeriv L θ c = 0 := ⟨F1 _, hF1 _⟩
  obtain ⟨φ, hφ, hφc, hφ1c⟩ : ∃ φ, IsSolution L (s * Complex.I) 0 φ ∧ φ c = 0 ∧
      quasiDeriv L φ c = 1 := ⟨F2 _, hF2 _⟩
  have hW : ∀ x ∈ L.I, wronskian L x θ φ = 1 := by
    intro x hx
    have := wronskian_sub L _ 0 θ φ hθ hφ hc hx
    simp only [Pi.zero_apply, mul_zero, zero_mul, intervalIntegral.integral_zero] at this
    rw [sub_eq_zero.mp this]
    unfold wronskian; rw [hθc, hθ1c, hφc, hφ1c]; ring
  have hcomb := fun m : ℂ => isSolution_comb L hθ hφ m
  set Q : ℂ → ℝ → ℝ := fun m y => (starRingEnd ℂ (θ y + m * φ y) *
    (quasiDeriv L θ y + m * quasiDeriv L φ y)).im with hQ
  have hQW : ∀ m, ∀ y ∈ L.I, imW L (fun x => θ x + m * φ x) y = Q m y := by
    intro m y hy; simp only [imW, hQ]; rw [(hcomb m).2 y hy]
  have hQc : ∀ m, Q m c = m.im := by intro m; simp [hQ, hθc, hφc, hθ1c, hφ1c]
  have hQN : ∀ m, ∀ y ∈ L.I, Side s c y →
      Q m y = m.im + Nrm L (fun x => θ x + m * φ x) y c := by
    intro m y hy hsd
    have hE := energy_side L (hcomb m).1 hc hy hsd
    rw [hQW m y hy, hQW m c hc, hQc] at hE
    have e : ∫ t in Ι y c, L.r t * (‖(fun x => θ x + m * φ x) t‖ ^ 2 +
        s * (starRingEnd ℂ ((fun x => θ x + m * φ x) t) * (0 : ℝ → ℂ) t).im) =
        Nrm L (fun x => θ x + m * φ x) y c := by
      unfold Nrm; congr 1; funext t; simp
    linarith
  set D : ℝ → Set ℂ := fun y => {m | Q m y ≤ 0} with hD
  have hclosed : ∀ y, IsClosed (D y) := by
    intro y
    refine isClosed_le ?_ continuous_const
    exact Complex.continuous_im.comp ((Complex.continuous_conj.comp
      (continuous_const.add (continuous_id.mul continuous_const))).mul
      (continuous_const.add (continuous_id.mul continuous_const)))
  let ι := {y : ℝ // y ∈ L.I ∧ Side s c y}
  obtain ⟨y0, hy0, hsd0⟩ := exists_side L hc hs
  haveI : Nonempty ι := ⟨⟨y0, hy0, hsd0⟩⟩
  have hsub : ∀ i j : ι, Ι i.1 c ⊆ Ι j.1 c → D j.1 ⊆ D i.1 := by
    intro i j hij m hm
    simp only [hD, mem_setOf_eq] at hm ⊢
    rw [hQN m i.1 i.2.1 i.2.2]
    rw [hQN m j.1 j.2.1 j.2.2] at hm
    have := Nrm_mono L (sol_contOn L (hcomb m).1) hc j.2.1 hij
    linarith
  have hdir : Directed (fun x1 x2 => x1 ⊇ x2) (fun i : ι => D i.1) := by
    intro i j
    rcases side_total i.2.2 j.2.2 with h | h
    · exact ⟨j, hsub i j h, subset_rfl⟩
    · exact ⟨i, subset_rfl, hsub j i h⟩
  have hne : ∀ i : ι, (D i.1).Nonempty := by
    intro i
    have hy := i.2.1
    by_cases hφy : φ i.1 = 0
    · have hWy := hW i.1 hy
      unfold wronskian at hWy
      rw [hφy, mul_zero, sub_zero] at hWy
      have hq : quasiDeriv L φ i.1 ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hWy; exact zero_ne_one hWy
      refine ⟨-(quasiDeriv L θ i.1) / quasiDeriv L φ i.1, ?_⟩
      simp only [hD, mem_setOf_eq, hQ]
      rw [div_mul_cancel₀ _ hq]; simp
    · refine ⟨-(θ i.1) / φ i.1, ?_⟩
      simp only [hD, mem_setOf_eq, hQ]
      rw [div_mul_cancel₀ _ hφy]; simp
  have hbdd : ∀ i : ι, Bornology.IsBounded (D i.1) := by
    intro i
    have hy := i.2.1
    have hyc : i.1 ≠ c := by
      rcases i.2.2 with ⟨-, h⟩ | ⟨-, h⟩
      · exact h.ne
      · exact h.ne'
    set Nφ := Nrm L φ i.1 c
    set Nθ := Nrm L θ i.1 c
    have hNφ : 0 < Nφ := Nrm_pos L hθ hφ hW hc hy hyc
    have hNθ : 0 ≤ Nθ := Nrm_nonneg L θ hy hc
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1 + (2 + 2 * Nθ) / Nφ, fun m hm => ?_⟩
    simp only [hD, mem_setOf_eq] at hm
    rw [hQN m i.1 hy i.2.2] at hm
    rw [Metric.mem_closedBall, dist_zero_right]
    set Nm := Nrm L (fun x => θ x + m * φ x) i.1 c
    have him : -m.im ≤ ‖m‖ := by
      have := Complex.abs_im_le_norm m; rw [abs_le] at this; linarith
    have hNm : Nm ≤ ‖m‖ := by linarith
    have hcθ := sol_contOn L hθ
    have hcφ := sol_contOn L hφ
    have hcψ := sol_contOn L (hcomb m).1
    have hineq : ‖m‖ ^ 2 * Nφ ≤ 2 * Nm + 2 * Nθ := by
      have i1 := int_r_norm_sq L hcφ hy hc
      have i2 := int_r_norm_sq L hcψ hy hc
      have i3 := int_r_norm_sq L hcθ hy hc
      have e1 : ‖m‖ ^ 2 * Nφ = ∫ t in Ι i.1 c, ‖m‖ ^ 2 * (L.r t * ‖φ t‖ ^ 2) := by
        rw [integral_const_mul]; rfl
      have e2 : 2 * Nm + 2 * Nθ = ∫ t in Ι i.1 c,
          (2 * (L.r t * ‖θ t + m * φ t‖ ^ 2) + 2 * (L.r t * ‖θ t‖ ^ 2)) := by
        rw [integral_add (i2.const_mul 2) (i3.const_mul 2), integral_const_mul,
          integral_const_mul]; rfl
      rw [e1, e2]
      refine setIntegral_mono_on (i1.const_mul _) ((i2.const_mul 2).add (i3.const_mul 2))
        measurableSet_uIoc fun t ht => ?_
      have hr := r_nonneg_of_mem L (uIoc_sub_I L hy hc ht)
      have hmφ : ‖m‖ * ‖φ t‖ ≤ ‖θ t + m * φ t‖ + ‖θ t‖ := by
        rw [← norm_mul]
        calc ‖m * φ t‖ = ‖(θ t + m * φ t) - θ t‖ := by ring_nf
          _ ≤ ‖θ t + m * φ t‖ + ‖θ t‖ := norm_sub_le _ _
      have h2 : (‖m‖ * ‖φ t‖) ^ 2 ≤ 2 * ‖θ t + m * φ t‖ ^ 2 + 2 * ‖θ t‖ ^ 2 := by
        nlinarith [sq_nonneg (‖θ t + m * φ t‖ - ‖θ t‖), norm_nonneg (θ t + m * φ t),
          norm_nonneg (θ t), mul_nonneg (norm_nonneg m) (norm_nonneg (φ t))]
      nlinarith
    rcases le_or_gt ‖m‖ 1 with h1 | h1
    · have : 0 ≤ (2 + 2 * Nθ) / Nφ := div_nonneg (by linarith) hNφ.le
      linarith
    · have h3 : ‖m‖ * Nφ ≤ 2 + 2 * Nθ := by
        have : ‖m‖ ^ 2 * Nφ ≤ (2 + 2 * Nθ) * ‖m‖ := by nlinarith
        nlinarith
      have : ‖m‖ ≤ (2 + 2 * Nθ) / Nφ := by rw [le_div_iff₀ hNφ]; exact h3
      linarith
  have hcpt : ∀ i : ι, IsCompact (D i.1) := fun i =>
    Metric.isCompact_of_isClosed_isBounded (hclosed _) (hbdd i)
  obtain ⟨m, hm⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fun i : ι => D i.1) hdir hne hcpt (fun i => hclosed _)
  rw [mem_iInter] at hm
  refine ⟨fun x => θ x + m * φ x, φ, (hcomb m).1, hφ, fun x hx => ?_, by simp [hθc, hφc], hφc,
    fun y hy hsd => ?_, -m.im, fun y hy hsd => ?_⟩
  · have := hW x hx
    unfold wronskian at this ⊢
    rw [(hcomb m).2 x hx]
    linear_combination this
  · rw [hQW m y hy]; exact hm ⟨y, hy, hsd⟩
  · have h1 := hm ⟨y, hy, hsd⟩
    simp only [hD, mem_setOf_eq] at h1
    rw [hQN m y hy hsd] at h1
    linarith

end WeylLP


open MeasureTheory Set Filter Topology
open scoped Interval

namespace WeylLP

open TeschlQM.SturmLiouville VoCAux LagAux IvpAux WeylAux

theorem isSolution_sub2 (L : SLData) {z : ℂ} {h f u1 u2 : ℝ → ℂ} (hf : IsSolution L z h f)
    (h1 : IsSolution L z 0 u1) (h2 : IsSolution L z 0 u2) (a b : ℂ) :
    IsSolution L z h (fun x => f x - a * u1 x - b * u2 x) ∧
      ∀ x ∈ L.I, quasiDeriv L (fun x => f x - a * u1 x - b * u2 x) x =
        quasiDeriv L f x - a * quasiDeriv L u1 x - b * quasiDeriv L u2 x := by
  obtain ⟨s1, q1⟩ := isSolution_lin L h1 h2 (-a) (-b)
  obtain ⟨s2, q2⟩ := isSolution_lin L hf s1 1 1
  have e1 : (fun x => (1 : ℂ) * f x + 1 * (-a * u1 x + -b * u2 x)) =
      fun x => f x - a * u1 x - b * u2 x := by funext x; ring
  have e2 : (fun x => (1 : ℂ) * h x + 1 * (-a * (0 : ℝ → ℂ) x + -b * (0 : ℝ → ℂ) x)) = h := by
    funext x; simp
  rw [e1, e2] at s2
  rw [e1] at q2
  exact ⟨s2, fun x hx => by rw [q2 x hx, q1 x hx]; ring⟩

theorem phr_loc (L : SLData) {z : ℂ} {h G u : ℝ → ℂ} (hG : IsSolution L z h G)
    (hu : ContinuousOn u L.I) :
    LocallyIntegrableOn (fun t => u t * h t * (L.r t : ℂ)) L.I := by
  have e : (fun t => u t * h t * (L.r t : ℂ)) = fun t => u t * ((L.r t : ℂ) * h t) := by
    funext t; ring
  rw [e]
  exact (rh_loc L hG).continuousOn_mul hu (I_lc L)

theorem Nrm_le_total (L : SLData) {u : ℝ → ℂ}
    (hu : IntegrableOn (fun t => L.r t * ‖u t‖ ^ 2) L.I) {y c : ℝ} (hy : y ∈ L.I)
    (hc : c ∈ L.I) : Nrm L u y c ≤ ∫ t in L.I, L.r t * ‖u t‖ ^ 2 :=
  setIntegral_mono_set hu
    ((ae_restrict_iff' (I_isOpen L).measurableSet).mpr (Eventually.of_forall fun t ht =>
      mul_nonneg (r_nonneg_of_mem L ht) (sq_nonneg _)))
    (Eventually.of_forall (uIoc_sub_I L hy hc))

theorem integrable_of_memLp (L : SLData) {u : ℝ → ℂ} (hu : MemLp u 2 L.measure) :
    IntegrableOn (fun t => L.r t * ‖u t‖ ^ 2) L.I :=
  memLp_integrable L (I_isOpen L).measurableSet subset_rfl hu

theorem imW_smul (L : SLData) {G ψ : ℝ → ℂ} {y : ℝ} (k : ℂ) (h1 : G y = ψ y * k)
    (h2 : quasiDeriv L G y = quasiDeriv L ψ y * k) :
    imW L G y = ‖k‖ ^ 2 * imW L ψ y := by
  unfold imW
  rw [h1, h2]
  have : starRingEnd ℂ (ψ y * k) * (quasiDeriv L ψ y * k) =
      (starRingEnd ℂ (ψ y) * quasiDeriv L ψ y) * ((‖k‖ ^ 2 : ℝ) : ℂ) := by
    rw [map_mul]; push_cast; rw [← Complex.conj_mul']; ring
  rw [this, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring

/-- Representation of an element of the maximal domain near the endpoint in terms of the Weyl
solution `ψ` and the second solution `φ`, with the coefficient bound
`|B(y)|² ∫_y^c r|φ|² ≤ K`. -/
theorem rep (L : SLData) {s c : ℝ} (hc : c ∈ L.I) {ψ φ : ℝ → ℂ}
    (hψ : IsSolution L (s * Complex.I) 0 ψ) (hφ : IsSolution L (s * Complex.I) 0 φ)
    (hW : ∀ x ∈ L.I, wronskian L x ψ φ = 1) (hψc : ψ c = 1) (hφc : φ c = 0)
    (himW : ∀ y ∈ L.I, Side s c y → imW L ψ y ≤ 0) {Mψ : ℝ}
    (hMψ : ∀ y ∈ L.I, Side s c y → Nrm L ψ y c ≤ Mψ) {f : ℝ → ℂ} (hf : InMaxDomain L f) :
    ∃ A B h : ℝ → ℂ,
      (∀ x ∈ L.I, f x = ψ x * A x + φ x * B x ∧
        quasiDeriv L f x = quasiDeriv L ψ x * A x + quasiDeriv L φ x * B x) ∧
      IsSolution L (s * Complex.I) h f ∧
      IntegrableOn (fun t => L.r t * ‖h t‖ ^ 2) L.I ∧
      (∀ x ∈ L.I, ∀ y ∈ L.I, A y - A x = ∫ t in x..y, φ t * h t * (L.r t : ℂ)) ∧
      ∃ K, ∀ y ∈ L.I, Side s c y → ‖B y‖ ^ 2 * Nrm L φ y c ≤ K := by
  obtain ⟨hfm, g, hgs, hgm⟩ := hf
  set z : ℂ := s * Complex.I with hz
  set h : ℝ → ℂ := fun x => g x - z * f x with hh
  have hfs : IsSolution L z h f := by
    have e : (fun x => z * f x + h x) = g := by funext x; simp only [hh]; ring
    unfold IsSolution; rw [e]; exact hgs
  obtain ⟨α, β, hrep⟩ := voc L z h ψ φ hψ hφ hW c hc f hfs
  set A : ℝ → ℂ := fun x => α + ∫ y in c..x, φ y * h y * (L.r y : ℂ) with hA
  set B : ℝ → ℂ := fun x => β - ∫ y in c..x, ψ y * h y * (L.r y : ℂ) with hB
  have hR1 : ∀ x ∈ L.I, f x = ψ x * A x + φ x * B x ∧
      quasiDeriv L f x = quasiDeriv L ψ x * A x + quasiDeriv L φ x * B x := hrep
  have hhm : MemLp h 2 L.measure := hgm.sub (hfm.const_mul z)
  have hhi := integrable_of_memLp L hhm
  have hfi := integrable_of_memLp L hfm
  have hφl := phr_loc L hfs (sol_contOn L hφ)
  refine ⟨A, B, h, hR1, hfs, hhi, fun x hx y hy => ?_, ?_⟩
  · simp only [hA]
    rw [add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left
      (ii_of_loc L hφl hc hy) (ii_of_loc L hφl hc hx)]
  set Ftot := ∫ t in L.I, L.r t * ‖f t‖ ^ 2
  set Htot := ∫ t in L.I, L.r t * ‖h t‖ ^ 2
  refine ⟨3 * (Ftot + ‖α‖ ^ 2 * Mψ + Htot), fun y hy hsd => ?_⟩
  obtain ⟨hG, hGq⟩ := isSolution_sub2 L hfs hψ hφ α (B y)
  set G : ℝ → ℂ := fun x => f x - α * ψ x - B y * φ x with hGdef
  have hfc : f c = α := by
    rw [(hR1 c hc).1, hψc, hφc]; simp [hA]
  have hGc : G c = 0 := by simp only [hGdef, hfc, hψc, hφc]; ring
  have hGy : imW L G y ≤ 0 := by
    rw [imW_smul L (A y - α) (ψ := ψ) (by simp only [hGdef]; rw [(hR1 y hy).1]; ring)
      (by rw [hGq y hy, (hR1 y hy).2]; ring)]
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (himW y hy hsd)
  have hNG : Nrm L G y c ≤ Htot :=
    (mass_le L hG hc hy hsd hGc hGy (hhi.mono_set (uIoc_sub_I L hy hc))).trans
      (Nrm_le_total L hhi hy hc)
  have hNf : Nrm L f y c ≤ Ftot := Nrm_le_total L hfi hy hc
  have hNψ := hMψ y hy hsd
  have cf := sol_contOn L hfs
  have cψ := sol_contOn L hψ
  have cφ := sol_contOn L hφ
  have cG := sol_contOn L hG
  have i1 := int_r_norm_sq L cφ hy hc
  have i2 := int_r_norm_sq L cf hy hc
  have i3 := int_r_norm_sq L cψ hy hc
  have i4 := int_r_norm_sq L cG hy hc
  have j3 : IntegrableOn (fun t => 3 * (L.r t * ‖f t‖ ^ 2)) (Ι y c) := i2.const_mul 3
  have j4 : IntegrableOn (fun t => 3 * ‖α‖ ^ 2 * (L.r t * ‖ψ t‖ ^ 2)) (Ι y c) := i3.const_mul _
  have j1 : IntegrableOn (fun t => 3 * (L.r t * ‖f t‖ ^ 2) +
      3 * ‖α‖ ^ 2 * (L.r t * ‖ψ t‖ ^ 2)) (Ι y c) := j3.add j4
  have j2 : IntegrableOn (fun t => 3 * (L.r t * ‖G t‖ ^ 2)) (Ι y c) := i4.const_mul 3
  have key : ‖B y‖ ^ 2 * Nrm L φ y c ≤
      3 * (Nrm L f y c + ‖α‖ ^ 2 * Nrm L ψ y c + Nrm L G y c) := by
    have e1 : ‖B y‖ ^ 2 * Nrm L φ y c = ∫ t in Ι y c, ‖B y‖ ^ 2 * (L.r t * ‖φ t‖ ^ 2) := by
      unfold Nrm; rw [integral_const_mul]
    have e2 : 3 * (Nrm L f y c + ‖α‖ ^ 2 * Nrm L ψ y c + Nrm L G y c) =
        ∫ t in Ι y c, (3 * (L.r t * ‖f t‖ ^ 2) + 3 * ‖α‖ ^ 2 * (L.r t * ‖ψ t‖ ^ 2) +
          3 * (L.r t * ‖G t‖ ^ 2)) := by
      unfold Nrm
      rw [integral_add j1 j2, integral_add j3 j4, integral_const_mul, integral_const_mul,
        integral_const_mul]
      ring
    rw [e1, e2]
    refine setIntegral_mono_on (i1.const_mul _) (j1.add j2) measurableSet_uIoc fun t ht => ?_
    have hr := r_nonneg_of_mem L (uIoc_sub_I L hy hc ht)
    have hBt : ‖B y‖ * ‖φ t‖ ≤ ‖f t‖ + ‖α‖ * ‖ψ t‖ + ‖G t‖ := by
      rw [← norm_mul, ← norm_mul]
      calc ‖B y * φ t‖ = ‖f t - α * ψ t - G t‖ := by simp only [hGdef]; ring_nf
        _ ≤ ‖f t - α * ψ t‖ + ‖G t‖ := norm_sub_le _ _
        _ ≤ ‖f t‖ + ‖α * ψ t‖ + ‖G t‖ := by gcongr; exact norm_sub_le _ _
    have h3 : (‖B y‖ * ‖φ t‖) ^ 2 ≤ 3 * ‖f t‖ ^ 2 + 3 * (‖α‖ * ‖ψ t‖) ^ 2 + 3 * ‖G t‖ ^ 2 := by
      have hn : 0 ≤ ‖B y‖ * ‖φ t‖ := by positivity
      nlinarith [sq_nonneg (‖f t‖ - ‖α‖ * ‖ψ t‖), sq_nonneg (‖f t‖ - ‖G t‖),
        sq_nonneg (‖α‖ * ‖ψ t‖ - ‖G t‖)]
    have : ‖B y‖ ^ 2 * (L.r t * ‖φ t‖ ^ 2) = L.r t * (‖B y‖ * ‖φ t‖) ^ 2 := by ring
    rw [this]
    have h4 := mul_le_mul_of_nonneg_left h3 hr
    nlinarith
  have hα : 0 ≤ ‖α‖ ^ 2 := sq_nonneg _
  nlinarith

end WeylLP


open MeasureTheory Set Filter Topology
open scoped Interval

namespace WeylLP

open TeschlQM.SturmLiouville VoCAux LagAux IvpAux WeylAux

/-- `y` lies beyond `x` (seen from `c`) on the `s`-side. -/
def Bey (s x y : ℝ) : Prop := (s = 1 ∧ y ≤ x) ∨ (s = -1 ∧ x ≤ y)

theorem bey_side {s c x y : ℝ} (hx : Side s c x) (h : Bey s x y) : Side s c y := by
  rcases hx with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> rcases h with ⟨h1, h⟩ | ⟨h1, h⟩ <;>
    try norm_num at h1
  · exact Or.inl ⟨rfl, lt_of_le_of_lt h hx⟩
  · exact Or.inr ⟨rfl, lt_of_lt_of_le hx h⟩

theorem bey_sub {s c x y : ℝ} (hx : Side s c x) (h : Bey s x y) :
    Ι x c ⊆ Ι y c ∧ Ι x y ⊆ Ι y c ∧ Ι y c = Ι x y ∪ Ι x c ∧ Disjoint (Ι x y) (Ι x c) := by
  rcases hx with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> rcases h with ⟨h1, h⟩ | ⟨h1, h⟩ <;>
    try norm_num at h1
  · rw [uIoc_of_le hx.le, uIoc_of_le (h.trans hx.le), uIoc_of_ge h]
    refine ⟨Ioc_subset_Ioc_left h, Ioc_subset_Ioc_right hx.le, (Ioc_union_Ioc_eq_Ioc h hx.le).symm,
      ?_⟩
    rw [Set.disjoint_left]; intro t ht1 ht2; exact absurd ht1.2 (not_le.mpr ht2.1)
  · rw [uIoc_of_ge hx.le, uIoc_of_ge (hx.le.trans h), uIoc_of_le h]
    refine ⟨Ioc_subset_Ioc_right h, Ioc_subset_Ioc_left hx.le, ?_, ?_⟩
    · rw [union_comm]; exact (Ioc_union_Ioc_eq_Ioc hx.le h).symm
    · rw [Set.disjoint_left]; intro t ht1 ht2; exact absurd ht2.2 (not_le.mpr ht1.1)

/-- Tails of an integrable weight become small beyond some point. -/
theorem tail_small (L : SLData) {s c : ℝ} (hc : c ∈ L.I) (hs : s = 1 ∨ s = -1) {h : ℝ → ℂ}
    (hh : IntegrableOn (fun t => L.r t * ‖h t‖ ^ 2) L.I) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ L.I, Side s c x ∧ ∀ y ∈ L.I, Bey s x y →
      ∫ t in Ι x y, L.r t * ‖h t‖ ^ 2 ≤ ε := by
  set T := {v : ℝ | ∃ y ∈ L.I, Side s c y ∧ v = Nrm L h y c}
  have hne : T.Nonempty := by
    obtain ⟨y, hy, hsd⟩ := exists_side L hc hs
    exact ⟨_, y, hy, hsd, rfl⟩
  have hbdd : BddAbove T := ⟨_, fun v ⟨y, hy, _, hv⟩ => hv ▸ Nrm_le_total L hh hy hc⟩
  obtain ⟨v, ⟨x, hx, hsx, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne (sub_lt_self (sSup T) hε)
  refine ⟨x, hx, hsx, fun y hy hb => ?_⟩
  obtain ⟨-, hxy, hsplit, hdisj⟩ := bey_sub hsx hb
  have hyT : Nrm L h y c ≤ sSup T := le_csSup hbdd ⟨y, hy, bey_side hsx hb, rfl⟩
  have hint : IntegrableOn (fun t => L.r t * ‖h t‖ ^ 2) (Ι y c) :=
    hh.mono_set (uIoc_sub_I L hy hc)
  have hsum : Nrm L h y c = (∫ t in Ι x y, L.r t * ‖h t‖ ^ 2) + Nrm L h x c := by
    unfold Nrm
    rw [hsplit, setIntegral_union hdisj measurableSet_uIoc (hint.mono_set (hsplit ▸
      subset_union_left)) (hint.mono_set (hsplit ▸ subset_union_right))]
  linarith

/-- The abstract limit: `A(y) B(y) → 0`. -/
theorem AB_tendsto (L : SLData) {s c : ℝ} (hc : c ∈ L.I) (hs : s = 1 ∨ s = -1)
    {φ : ℝ → ℂ} (hφ : ContinuousOn φ L.I)
    (hunb : ∀ M, ∃ y ∈ L.I, Side s c y ∧ M < Nrm L φ y c)
    {F : Filter ℝ} (hF1 : ∀ᶠ y in F, y ∈ L.I ∧ Side s c y)
    (hF2 : ∀ x ∈ L.I, Side s c x → ∀ᶠ y in F, Bey s x y)
    {A B h : ℝ → ℂ} (hA : ∀ x ∈ L.I, ∀ y ∈ L.I, A y - A x = ∫ t in x..y, φ t * h t * (L.r t : ℂ))
    (hloc : LocallyIntegrableOn (fun t => φ t * h t * (L.r t : ℂ)) L.I)
    (hh : IntegrableOn (fun t => L.r t * ‖h t‖ ^ 2) L.I) {K : ℝ}
    (hB : ∀ y ∈ L.I, Side s c y → ‖B y‖ ^ 2 * Nrm L φ y c ≤ K) :
    Tendsto (fun y => A y * B y) F (𝓝 0) := by
  set K' := max K 0 with hK'def
  have hB' : ∀ y ∈ L.I, Side s c y → ‖B y‖ ^ 2 * Nrm L φ y c ≤ K' :=
    fun y hy hsd => (hB y hy hsd).trans (le_max_left _ _)
  have hK' : 0 ≤ K' := le_max_right _ _
  have hNinf : ∀ M, ∀ᶠ y in F, M ≤ Nrm L φ y c := by
    intro M
    obtain ⟨x0, hx0, hsx0, hlt⟩ := hunb M
    filter_upwards [hF1, hF2 x0 hx0 hsx0] with y hy hb
    exact hlt.le.trans (Nrm_mono L hφ hc hy.1 (bey_sub hsx0 hb).1)
  have hBsmall : ∀ δ > 0, ∀ᶠ y in F, ‖B y‖ < δ := by
    intro δ hδ
    filter_upwards [hF1, hNinf (K' / δ ^ 2 + 1)] with y hy hN
    by_contra hcon
    push_neg at hcon
    have h1 := hB' y hy.1 hy.2
    have hδ2 : δ ^ 2 ≤ ‖B y‖ ^ 2 := by nlinarith
    have hpos : 0 < K' / δ ^ 2 + 1 := by positivity
    have h2 : δ ^ 2 * (K' / δ ^ 2 + 1) ≤ ‖B y‖ ^ 2 * Nrm L φ y c :=
      mul_le_mul hδ2 hN hpos.le (sq_nonneg _)
    have e : δ ^ 2 * (K' / δ ^ 2 + 1) = K' + δ ^ 2 := by field_simp
    nlinarith [sq_pos_of_pos hδ]
  rw [Metric.tendsto_nhds]
  intro ε hε
  set tt := ε / (2 * (K' + 1)) with htt
  have htpos : 0 < tt := by positivity
  have htK : tt * K' ≤ ε / 2 := by
    rw [htt, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨x, hx, hsx, htail⟩ := tail_small L hc hs hh (ε := tt * (ε / 2)) (by positivity)
  filter_upwards [hF1, hF2 x hx hsx, hBsmall (ε / 2 / (‖A x‖ + 1)) (by positivity)]
    with y hy hb hBy
  rw [dist_zero_right, norm_mul]
  obtain ⟨-, hxy, -, -⟩ := bey_sub hsx hb
  have hAy : A y = A x + ∫ t in x..y, φ t * h t * (L.r t : ℂ) := by
    rw [← hA x hx y hy.1]; ring
  have hint : IntegrableOn (fun t => φ t * h t * (L.r t : ℂ)) (Ι x y) :=
    (hloc.integrableOn_compact_subset (uIcc_subset_I L hx hy.1) isCompact_uIcc).mono_set
      uIoc_subset_uIcc
  have hφi : IntegrableOn (fun t => L.r t * ‖φ t‖ ^ 2) (Ι x y) :=
    (int_r_norm_sq L hφ hy.1 hc).mono_set hxy
  have hhi : IntegrableOn (fun t => L.r t * ‖h t‖ ^ 2) (Ι x y) :=
    hh.mono_set (uIoc_sub_I L hx hy.1)
  have hφN : ∫ t in Ι x y, L.r t * ‖φ t‖ ^ 2 ≤ Nrm L φ y c :=
    setIntegral_mono_set (int_r_norm_sq L hφ hy.1 hc)
      ((ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun t ht =>
        mul_nonneg (r_nonneg_of_mem L (uIoc_sub_I L hy.1 hc ht)) (sq_nonneg _)))
      (Eventually.of_forall hxy)
  have hI1 : ‖∫ t in x..y, φ t * h t * (L.r t : ℂ)‖ * ‖B y‖ ≤ ε / 2 := by
    have hpt : ∀ u ∈ Ι x y, ‖B y‖ * ‖φ u * h u * (L.r u : ℂ)‖ ≤
        (1 / 2) * (tt * ‖B y‖ ^ 2) * (L.r u * ‖φ u‖ ^ 2) +
          (1 / 2) * (1 / tt) * (L.r u * ‖h u‖ ^ 2) := by
      intro u hu
      have hr := r_nonneg_of_mem L (uIoc_sub_I L hx hy.1 hu)
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr]
      have key : (‖B y‖ * ‖φ u‖) * ‖h u‖ ≤
          (1 / 2) * tt * (‖B y‖ * ‖φ u‖) ^ 2 + (1 / 2) * (1 / tt) * ‖h u‖ ^ 2 := by
        have h0 : 0 ≤ (tt * (‖B y‖ * ‖φ u‖) - ‖h u‖) ^ 2 := sq_nonneg _
        have e : (1 / 2) * tt * (‖B y‖ * ‖φ u‖) ^ 2 + (1 / 2) * (1 / tt) * ‖h u‖ ^ 2 -
            (‖B y‖ * ‖φ u‖) * ‖h u‖ = (tt * (‖B y‖ * ‖φ u‖) - ‖h u‖) ^ 2 / (2 * tt) := by
          field_simp; ring
        have : 0 ≤ (tt * (‖B y‖ * ‖φ u‖) - ‖h u‖) ^ 2 / (2 * tt) := by positivity
        linarith
      have := mul_le_mul_of_nonneg_left key hr
      nlinarith
    have j1 : IntegrableOn (fun t => (1 / 2) * (tt * ‖B y‖ ^ 2) * (L.r t * ‖φ t‖ ^ 2))
        (Ι x y) := hφi.const_mul _
    have j2 : IntegrableOn (fun t => (1 / 2) * (1 / tt) * (L.r t * ‖h t‖ ^ 2)) (Ι x y) :=
      hhi.const_mul _
    have j3 : IntegrableOn (fun t => (1 / 2) * (tt * ‖B y‖ ^ 2) * (L.r t * ‖φ t‖ ^ 2) +
        (1 / 2) * (1 / tt) * (L.r t * ‖h t‖ ^ 2)) (Ι x y) := j1.add j2
    calc ‖∫ t in x..y, φ t * h t * (L.r t : ℂ)‖ * ‖B y‖
        ≤ (∫ t in Ι x y, ‖φ t * h t * (L.r t : ℂ)‖) * ‖B y‖ :=
          mul_le_mul_of_nonneg_right intervalIntegral.norm_integral_le_integral_norm_uIoc
            (norm_nonneg _)
      _ = ∫ t in Ι x y, ‖B y‖ * ‖φ t * h t * (L.r t : ℂ)‖ := by
          rw [integral_const_mul]; ring
      _ ≤ ∫ t in Ι x y, ((1 / 2) * (tt * ‖B y‖ ^ 2) * (L.r t * ‖φ t‖ ^ 2) +
            (1 / 2) * (1 / tt) * (L.r t * ‖h t‖ ^ 2)) :=
          setIntegral_mono_on (hint.norm.const_mul _) j3 measurableSet_uIoc hpt
      _ = (1 / 2) * (tt * ‖B y‖ ^ 2) * (∫ t in Ι x y, L.r t * ‖φ t‖ ^ 2) +
            (1 / 2) * (1 / tt) * (∫ t in Ι x y, L.r t * ‖h t‖ ^ 2) := by
          rw [integral_add j1 j2, integral_const_mul, integral_const_mul]
      _ ≤ (1 / 2) * (tt * K') + (1 / 2) * (1 / tt) * (tt * (ε / 2)) := by
          have h1 := hB' y hy.1 hy.2
          have h2 := htail y hy.1 hb
          have h3 : ‖B y‖ ^ 2 * (∫ t in Ι x y, L.r t * ‖φ t‖ ^ 2) ≤ K' :=
            (mul_le_mul_of_nonneg_left hφN (sq_nonneg _)).trans h1
          have h4 : 0 ≤ 1 / tt := by positivity
          have h5 := mul_le_mul_of_nonneg_left h2 h4
          nlinarith
      _ ≤ ε / 2 := by
          have : (1 / 2) * (1 / tt) * (tt * (ε / 2)) = ε / 4 := by field_simp; ring
          rw [this]; linarith
  have hAx : ‖A x‖ * ‖B y‖ < ε / 2 := by
    have h1 : ‖B y‖ * (‖A x‖ + 1) < ε / 2 := by
      rwa [lt_div_iff₀ (by positivity)] at hBy
    nlinarith [norm_nonneg (B y)]
  calc ‖A y‖ * ‖B y‖ ≤ (‖A x‖ + ‖∫ t in x..y, φ t * h t * (L.r t : ℂ)‖) * ‖B y‖ := by
        rw [hAy]; exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (norm_nonneg _)
    _ < ε := by linarith

end WeylLP


open MeasureTheory Set Filter Topology
open scoped Interval

namespace WeylLP

open TeschlQM.SturmLiouville VoCAux LagAux IvpAux WeylAux

theorem memLp_of_integrable (L : SLData) {S : Set ℝ} (hS : MeasurableSet S) (hSI : S ⊆ L.I)
    {u : ℝ → ℂ} (hu : ContinuousOn u L.I) (hint : IntegrableOn (fun s => L.r s * ‖u s‖ ^ 2) S) :
    MemLp u 2 ((volume.restrict S).withDensity (fun x => ENNReal.ofReal (L.r x))) := by
  have hmeas : AEStronglyMeasurable u
      ((volume.restrict S).withDensity (fun x => ENNReal.ofReal (L.r x))) :=
    (hu.mono hSI).aestronglyMeasurable hS |>.mono_ac (withDensity_absolutelyContinuous _ _)
  refine (memLp_two_iff_integrable_sq_norm hmeas).mpr ?_
  have hr : AEMeasurable (fun x => (L.r x).toNNReal) (volume.restrict S) :=
    (L.r_loc.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono hSI le_rfl)).aemeasurable.real_toNNReal
  refine (integrable_withDensity_iff_integrable_smul₀ hr).mpr ?_
  refine hint.congr (ae_restrict_of_forall_mem hS (fun x hx => ?_))
  have hx0 := (L.r_pos x (hSI hx).1 (hSI hx).2).le
  simp only [NNReal.smul_def, Real.coe_toNNReal _ hx0, smul_eq_mul]

/-- Bounded mass on the left of `c` gives square integrability near `a`. -/
theorem memLp_of_Nrm_left (L : SLData) {c : ℝ} (hc : c ∈ L.I) {u : ℝ → ℂ}
    (hu : ContinuousOn u L.I) {M : ℝ} (hM : ∀ y ∈ L.I, y < c → Nrm L u y c ≤ M) :
    MemLp u 2 ((volume.restrict {x : ℝ | L.a < (x : EReal) ∧ x < c}).withDensity
      (fun x => ENNReal.ofReal (L.r x))) := by
  refine memLp_of_integrable L (measSL L c) (SL_sub L hc) hu ?_
  set k : ℝ → ℝ := fun s => L.r s * ‖u s‖ ^ 2
  classical
  set φs : ℝ → Set ℝ := fun i => if i ∈ L.I then Ioc i c else ∅
  have hcov : AECover (volume.restrict {x : ℝ | L.a < (x : EReal) ∧ x < c}) L.atLeft φs := by
    refine ⟨?_, fun i => ?_⟩
    · refine ae_restrict_of_forall_mem (measSL L c) fun x hx => ?_
      filter_upwards [eventually_mem_left L, eventually_lt_left L hx.1] with i hi hix
      simp only [φs, if_pos hi]
      exact ⟨hix, hx.2.le⟩
    · simp only [φs]; split_ifs
      · exact measurableSet_Ioc
      · exact MeasurableSet.empty
  refine hcov.integrable_of_integral_norm_bounded M (fun i => ?_) ?_
  · simp only [φs]
    split_ifs with hi
    · have h1 : IntegrableOn k (Ι i c) := int_r_norm_sq L hu hi hc
      rcases le_or_gt i c with hic | hic
      · rw [uIoc_of_le hic] at h1
        exact h1.mono_measure Measure.restrict_le_self
      · rw [Ioc_eq_empty (not_lt.mpr hic.le)]; exact integrableOn_empty
    · exact integrableOn_empty
  · filter_upwards [eventually_mem_left L, eventually_lt_left L hc.1] with i hi hic
    simp only [φs, if_pos hi]
    rw [Measure.restrict_restrict measurableSet_Ioc]
    have h1 : IntegrableOn k (Ι i c) := int_r_norm_sq L hu hi hc
    rw [uIoc_of_le hic.le] at h1
    calc ∫ x in Ioc i c ∩ {x : ℝ | L.a < (x : EReal) ∧ x < c}, ‖k x‖
        ≤ ∫ x in Ioc i c, ‖k x‖ :=
          setIntegral_mono_set h1.norm (Eventually.of_forall fun x => norm_nonneg _)
            (Eventually.of_forall inter_subset_left)
      _ = ∫ x in Ioc i c, k x := by
          refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
          have hxI : x ∈ L.I := uIoc_sub_I L hi hc (by rw [uIoc_of_le hic.le]; exact hx)
          exact Real.norm_of_nonneg (mul_nonneg (r_nonneg_of_mem L hxI) (sq_nonneg _))
      _ ≤ M := by
          have := hM i hi hic
          unfold Nrm at this; rwa [uIoc_of_le hic.le] at this

/-- Bounded mass on the right of `c` gives square integrability near `b`. -/
theorem memLp_of_Nrm_right (L : SLData) {c : ℝ} (hc : c ∈ L.I) {u : ℝ → ℂ}
    (hu : ContinuousOn u L.I) {M : ℝ} (hM : ∀ y ∈ L.I, c < y → Nrm L u y c ≤ M) :
    MemLp u 2 ((volume.restrict {x : ℝ | c < x ∧ (x : EReal) < L.b}).withDensity
      (fun x => ENNReal.ofReal (L.r x))) := by
  refine memLp_of_integrable L (measSR L c) (SR_sub L hc) hu ?_
  set k : ℝ → ℝ := fun s => L.r s * ‖u s‖ ^ 2
  classical
  set φs : ℝ → Set ℝ := fun i => if i ∈ L.I then Ioc c i else ∅
  have hcov : AECover (volume.restrict {x : ℝ | c < x ∧ (x : EReal) < L.b}) L.atRight φs := by
    refine ⟨?_, fun i => ?_⟩
    · refine ae_restrict_of_forall_mem (measSR L c) fun x hx => ?_
      filter_upwards [eventually_mem_right L, eventually_gt_right L hx.2] with i hi hix
      simp only [φs, if_pos hi]
      exact ⟨hx.1, hix.le⟩
    · simp only [φs]; split_ifs
      · exact measurableSet_Ioc
      · exact MeasurableSet.empty
  refine hcov.integrable_of_integral_norm_bounded M (fun i => ?_) ?_
  · simp only [φs]
    split_ifs with hi
    · have h1 : IntegrableOn k (Ι i c) := int_r_norm_sq L hu hi hc
      rcases le_or_gt c i with hic | hic
      · rw [uIoc_of_ge hic] at h1
        exact h1.mono_measure Measure.restrict_le_self
      · rw [Ioc_eq_empty (not_lt.mpr hic.le)]; exact integrableOn_empty
    · exact integrableOn_empty
  · filter_upwards [eventually_mem_right L, eventually_gt_right L hc.2] with i hi hic
    simp only [φs, if_pos hi]
    rw [Measure.restrict_restrict measurableSet_Ioc]
    have h1 : IntegrableOn k (Ι i c) := int_r_norm_sq L hu hi hc
    rw [uIoc_of_ge hic.le] at h1
    calc ∫ x in Ioc c i ∩ {x : ℝ | c < x ∧ (x : EReal) < L.b}, ‖k x‖
        ≤ ∫ x in Ioc c i, ‖k x‖ :=
          setIntegral_mono_set h1.norm (Eventually.of_forall fun x => norm_nonneg _)
            (Eventually.of_forall inter_subset_left)
      _ = ∫ x in Ioc c i, k x := by
          refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
          have hxI : x ∈ L.I := uIoc_sub_I L hi hc (by rw [uIoc_of_ge hic.le]; exact hx)
          exact Real.norm_of_nonneg (mul_nonneg (r_nonneg_of_mem L hxI) (sq_nonneg _))
      _ ≤ M := by
          have := hM i hi hic
          unfold Nrm at this; rwa [uIoc_of_ge hic.le] at this

end WeylLP


open MeasureTheory Set Filter Topology
open scoped Interval

namespace WeylLP

open TeschlQM.SturmLiouville VoCAux LagAux IvpAux WeylAux

/-- Core limit-point statement: if the second solution `φ` has unbounded mass on the `s`-side,
then `W_y(f, g) → 0` for all `f, g` in the maximal domain. -/
theorem lp_tendsto (L : SLData) {s c : ℝ} (hc : c ∈ L.I) (hs : s = 1 ∨ s = -1) {ψ φ : ℝ → ℂ}
    (hψ : IsSolution L (s * Complex.I) 0 ψ) (hφ : IsSolution L (s * Complex.I) 0 φ)
    (hW : ∀ x ∈ L.I, wronskian L x ψ φ = 1) (hψc : ψ c = 1) (hφc : φ c = 0)
    (himW : ∀ y ∈ L.I, Side s c y → imW L ψ y ≤ 0) {Mψ : ℝ}
    (hMψ : ∀ y ∈ L.I, Side s c y → Nrm L ψ y c ≤ Mψ)
    (hunb : ∀ M, ∃ y ∈ L.I, Side s c y ∧ M < Nrm L φ y c)
    {F : Filter ℝ} (hF1 : ∀ᶠ y in F, y ∈ L.I ∧ Side s c y)
    (hF2 : ∀ x ∈ L.I, Side s c x → ∀ᶠ y in F, Bey s x y)
    {f g : ℝ → ℂ} (hf : InMaxDomain L f) (hg : InMaxDomain L g) :
    Tendsto (fun y => wronskian L y f g) F (𝓝 0) := by
  obtain ⟨Af, Bf, hf_, hRf, hsf, hif, hAf, Kf, hKf⟩ :=
    rep L hc hψ hφ hW hψc hφc himW hMψ hf
  obtain ⟨Ag, Bg, hg_, hRg, hsg, hig, hAg, Kg, hKg⟩ :=
    rep L hc hψ hφ hW hψc hφc himW hMψ hg
  have cφ := sol_contOn L hφ
  have t1 := AB_tendsto L hc hs cφ hunb hF1 hF2 hAf (phr_loc L hsf cφ) hif hKg
  have t2 := AB_tendsto L hc hs cφ hunb hF1 hF2 hAg (phr_loc L hsg cφ) hig hKf
  have t3 := t1.sub t2
  rw [sub_zero] at t3
  refine t3.congr' ?_
  filter_upwards [hF1] with y hy
  have hWy := hW y hy.1
  unfold wronskian at hWy ⊢
  rw [(hRf y hy.1).1, (hRf y hy.1).2, (hRg y hy.1).1, (hRg y hy.1).2]
  linear_combination (-(Af y * Bg y - Ag y * Bf y)) * hWy

theorem comb_bound (a b α β : ℂ) :
    ‖a * α + b * β‖ ^ 2 ≤ 2 * (‖α‖ ^ 2 + ‖β‖ ^ 2) * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h1 := norm_add_le (a * α) (b * β)
  rw [norm_mul, norm_mul] at h1
  have h0 : 0 ≤ ‖a * α + b * β‖ := norm_nonneg _
  have h2 : ‖a * α + b * β‖ ^ 2 ≤ (‖a‖ * ‖α‖ + ‖b‖ * ‖β‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h3 : (‖a‖ * ‖α‖ + ‖b‖ * ‖β‖) ^ 2 ≤ 2 * (‖a‖ * ‖α‖) ^ 2 + 2 * (‖b‖ * ‖β‖) ^ 2 := by
    nlinarith [sq_nonneg (‖a‖ * ‖α‖ - ‖b‖ * ‖β‖)]
  nlinarith [sq_nonneg (‖a‖ * ‖β‖), sq_nonneg (‖b‖ * ‖α‖)]

/-- Limit point at `a` (in the solution sense, for `z = i`) forces `W_y(f, g) → 0`. -/
theorem lp_left (L : SLData)
    (hnot : ¬ ∀ u : ℝ → ℂ, IsSolution L (((1 : ℝ) : ℂ) * Complex.I) 0 u →
      IsSqIntegrableNearLeft L u)
    {f g : ℝ → ℂ} (hf : InMaxDomain L f) (hg : InMaxDomain L g) :
    Tendsto (fun y => wronskian L y f g) L.atLeft (𝓝 0) := by
  obtain ⟨c, hc⟩ := exists_mem_I L
  have hs : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1 := Or.inl rfl
  obtain ⟨ψ, φ, hψ, hφ, hW, hψc, hφc, himW, Mψ, hMψ⟩ := weyl_solution L hc hs
  have hside : ∀ y, Side 1 c y ↔ y < c := by
    intro y; constructor
    · rintro (⟨-, h⟩ | ⟨h1, -⟩)
      · exact h
      · norm_num at h1
    · intro h; exact Or.inl ⟨rfl, h⟩
  have hunb : ∀ M, ∃ y ∈ L.I, Side 1 c y ∧ M < Nrm L φ y c := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨M, hM⟩ := hcon
    apply hnot
    intro u hu
    have mψ := memLp_of_Nrm_left L hc (sol_contOn L hψ)
      (fun y hy hyc => hMψ y hy ((hside y).mpr hyc))
    have mφ := memLp_of_Nrm_left L hc (sol_contOn L hφ)
      (fun y hy hyc => hM y hy ((hside y).mpr hyc))
    obtain ⟨α, β, hrep⟩ := voc L _ 0 ψ φ hψ hφ hW c hc u hu
    refine ⟨c, hc, memLp_of_bound L (measSL L c) (SL_sub L hc) (sol_contOn L hu) mψ mφ
      (C := 2 * (‖α‖ ^ 2 + ‖β‖ ^ 2)) (by positivity) fun x hx => ?_⟩
    have hx' := (hrep x (SL_sub L hc hx)).1
    simp only [Pi.zero_apply, mul_zero, zero_mul, intervalIntegral.integral_zero, add_zero,
      sub_zero] at hx'
    rw [hx']
    exact comb_bound _ _ _ _
  refine lp_tendsto L hc hs hψ hφ hW hψc hφc himW hMψ hunb ?_ ?_ hf hg
  · filter_upwards [eventually_mem_left L, eventually_lt_left L hc.1] with y hy hyc
    exact ⟨hy, (hside y).mpr hyc⟩
  · intro x hx _
    filter_upwards [eventually_lt_left L hx.1] with y hy
    exact Or.inl ⟨rfl, hy.le⟩

/-- Limit point at `b` (in the solution sense, for `z = −i`) forces `W_y(f, g) → 0`. -/
theorem lp_right (L : SLData)
    (hnot : ¬ ∀ u : ℝ → ℂ, IsSolution L (((-1 : ℝ) : ℂ) * Complex.I) 0 u →
      IsSqIntegrableNearRight L u)
    {f g : ℝ → ℂ} (hf : InMaxDomain L f) (hg : InMaxDomain L g) :
    Tendsto (fun y => wronskian L y f g) L.atRight (𝓝 0) := by
  obtain ⟨c, hc⟩ := exists_mem_I L
  have hs : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1 := Or.inr rfl
  obtain ⟨ψ, φ, hψ, hφ, hW, hψc, hφc, himW, Mψ, hMψ⟩ := weyl_solution L hc hs
  have hside : ∀ y, Side (-1) c y ↔ c < y := by
    intro y; constructor
    · rintro (⟨h1, -⟩ | ⟨-, h⟩)
      · norm_num at h1
      · exact h
    · intro h; exact Or.inr ⟨rfl, h⟩
  have hunb : ∀ M, ∃ y ∈ L.I, Side (-1) c y ∧ M < Nrm L φ y c := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨M, hM⟩ := hcon
    apply hnot
    intro u hu
    have mψ := memLp_of_Nrm_right L hc (sol_contOn L hψ)
      (fun y hy hyc => hMψ y hy ((hside y).mpr hyc))
    have mφ := memLp_of_Nrm_right L hc (sol_contOn L hφ)
      (fun y hy hyc => hM y hy ((hside y).mpr hyc))
    obtain ⟨α, β, hrep⟩ := voc L _ 0 ψ φ hψ hφ hW c hc u hu
    refine ⟨c, hc, memLp_of_bound L (measSR L c) (SR_sub L hc) (sol_contOn L hu) mψ mφ
      (C := 2 * (‖α‖ ^ 2 + ‖β‖ ^ 2)) (by positivity) fun x hx => ?_⟩
    have hx' := (hrep x (SR_sub L hc hx)).1
    simp only [Pi.zero_apply, mul_zero, zero_mul, intervalIntegral.integral_zero, add_zero,
      sub_zero] at hx'
    rw [hx']
    exact comb_bound _ _ _ _
  refine lp_tendsto L hc hs hψ hφ hW hψc hφc himW hMψ hunb ?_ ?_ hf hg
  · filter_upwards [eventually_mem_right L, eventually_gt_right L hc.2] with y hy hyc
    exact ⟨hy, (hside y).mpr hyc⟩
  · intro x hx _
    filter_upwards [eventually_gt_right L hx.2] with y hy
    exact Or.inr ⟨rfl, hy.le⟩

/-- Teschl, Theorem 9.9 (hard direction): if `τ` is limit circle at an endpoint, then for some
`z₀` all solutions of `(τ − z₀) u = 0` are square integrable near that endpoint. -/
theorem sqIntegrable_of_limitCircle (L : SLData) :
    (IsLimitCircleLeft L →
      ∃ z₀ : ℂ, ∀ u : ℝ → ℂ, IsSolution L z₀ 0 u → IsSqIntegrableNearLeft L u) ∧
    (IsLimitCircleRight L →
      ∃ z₀ : ℂ, ∀ u : ℝ → ℂ, IsSolution L z₀ 0 u → IsSqIntegrableNearRight L u) := by
  constructor
  · rintro ⟨v, hv, -, f, hf, hne⟩
    refine ⟨((1 : ℝ) : ℂ) * Complex.I, ?_⟩
    by_contra hnot
    exact hne (lp_left L hnot hv hf).limUnder_eq
  · rintro ⟨v, hv, -, f, hf, hne⟩
    refine ⟨((-1 : ℝ) : ℂ) * Complex.I, ?_⟩
    by_contra hnot
    exact hne (lp_right L hnot hv hf).limUnder_eq

end WeylLP

open TeschlQM.SturmLiouville

theorem solution (L : SLData) :
    (IsLimitCircleLeft L →
      ∃ z₀ : ℂ, ∀ u : ℝ → ℂ, IsSolution L z₀ 0 u → IsSqIntegrableNearLeft L u) ∧
    (IsLimitCircleRight L →
      ∃ z₀ : ℂ, ∀ u : ℝ → ℂ, IsSolution L z₀ 0 u → IsSqIntegrableNearRight L u) :=
  WeylLP.sqIntegrable_of_limitCircle L

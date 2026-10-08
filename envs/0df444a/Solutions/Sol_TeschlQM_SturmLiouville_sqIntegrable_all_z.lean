-- Prove2me | solution 1 for TeschlQM.SturmLiouville.sqIntegrable_all_z
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-04T20:12:13.55199+00:00
-- url     : https://prove2.me/submissions/c4df2174-b12b-4bc5-88ce-f5a2bfc8f03f

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

open TeschlQM.SturmLiouville

theorem solution (L : SLData) :
    ((∃ z₀ : ℂ, ∀ u : ℝ → ℂ, IsSolution L z₀ 0 u → IsSqIntegrableNearLeft L u) →
      ∀ z : ℂ, ∀ u : ℝ → ℂ, IsSolution L z 0 u → IsSqIntegrableNearLeft L u) ∧
    ((∃ z₀ : ℂ, ∀ u : ℝ → ℂ, IsSolution L z₀ 0 u → IsSqIntegrableNearRight L u) →
      ∀ z : ℂ, ∀ u : ℝ → ℂ, IsSolution L z 0 u → IsSqIntegrableNearRight L u) :=
  WeylAux.sqIntegrable_all_z L

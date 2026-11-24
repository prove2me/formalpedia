-- Prove2me | solution 1 for RiemannVonMangoldt.dirichlet_L_zero_count
-- status  : ACCEPTED   (prove)
-- author  : @phi9t
-- created : 2026-11-24T10:32:08.34483+00:00
-- url     : https://prove2.me/submissions/985ab7a7-03af-4eb7-ace2-2c962ac9d69f

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts

/-! Source-faithful standalone candidate for the original Dirichlet zero-count parent.
The original count definition remains imported. The retained proofs below are copied
from pinned sources, with imports and diagnostic commands removed, and module scopes
made explicit. Source assembly is not kernel approval or platform acceptance. -/

/- Source module: ReciprocalRectangleV3
   Original SHA256: 748f93c1b1cdefc8204b4d413ca00f5214449ecd14bd3aa2c46bebe585235e6d -/
section P2MFinalSource001

/-!
Elementary reciprocal-kernel rectangle integral. The proof uses four actual
logarithm primitives, the real-parameter fundamental theorem of calculus, and
the pinned principal-argument identities. No argument principle is assumed.

Intended environment: Lean 4.33.1; Mathlib
0df444a360eaa60ab8c11dca51a86af692955474; autoImplicit=false.
This candidate requires ordinary kernel verification before use.
-/

set_option autoImplicit false

open Complex MeasureTheory
open scoped Interval

namespace RiemannVonMangoldt.RectKernel

lemma log_sub_log_neg_of_im_pos (w : ℂ) (hw : 0 < w.im) :
    Complex.log w - Complex.log (-w) = (Real.pi : ℂ) * I := by
  apply Complex.ext <;>
    simp [Complex.log_re, Complex.log_im,
      Complex.arg_neg_eq_arg_sub_pi_of_im_pos hw]

lemma log_sub_log_neg_of_im_neg (w : ℂ) (hw : w.im < 0) :
    Complex.log w - Complex.log (-w) = -((Real.pi : ℂ) * I) := by
  apply Complex.ext <;>
    simp [Complex.log_re, Complex.log_im,
      Complex.arg_neg_eq_arg_add_pi_of_im_neg hw]

lemma horizontal_denominator_ne_zero (rho : ℂ) (t : ℝ)
    (ht : t ≠ rho.im) (x : ℝ) :
    (x : ℂ) + (t : ℂ) * I - rho ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  have hz : t - rho.im = 0 := by simpa using hi
  exact ht (sub_eq_zero.mp hz)

lemma vertical_denominator_ne_zero (rho : ℂ) (r : ℝ)
    (hr : r ≠ rho.re) (y : ℝ) :
    (r : ℂ) + (y : ℂ) * I - rho ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have hz : r - rho.re = 0 := by simpa using hre
  exact hr (sub_eq_zero.mp hz)

lemma continuous_horizontal_reciprocal (rho : ℂ) (t : ℝ)
    (ht : t ≠ rho.im) :
    Continuous (fun x : ℝ => 1 / ((x : ℂ) + (t : ℂ) * I - rho)) := by
  have hc : Continuous (fun x : ℝ => (x : ℂ) + (t : ℂ) * I - rho) := by
    fun_prop
  exact continuous_const.div hc (horizontal_denominator_ne_zero rho t ht)

lemma continuous_vertical_reciprocal (rho : ℂ) (r : ℝ)
    (hr : r ≠ rho.re) :
    Continuous (fun y : ℝ => 1 / ((r : ℂ) + (y : ℂ) * I - rho)) := by
  have hc : Continuous (fun y : ℝ => (r : ℂ) + (y : ℂ) * I - rho) := by
    fun_prop
  exact continuous_const.div hc (vertical_denominator_ne_zero rho r hr)

lemma integral_horizontal_reciprocal (rho : ℂ) (t a b : ℝ)
    (ht : t ≠ rho.im) :
    (∫ x : ℝ in a..b, 1 / ((x : ℂ) + (t : ℂ) * I - rho)) =
      Complex.log ((b : ℂ) + (t : ℂ) * I - rho) -
      Complex.log ((a : ℂ) + (t : ℂ) * I - rho) := by
  have hd (x : ℝ) : HasDerivAt
      (fun x : ℝ => Complex.log ((x : ℂ) + (t : ℂ) * I - rho))
      (1 / ((x : ℂ) + (t : ℂ) * I - rho)) x := by
    have hs : (x : ℂ) + (t : ℂ) * I - rho ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      right
      simpa using sub_ne_zero.mpr ht
    have ha := (((hasDerivAt_id x).ofReal_comp).add_const ((t : ℂ) * I)).sub_const rho
    simpa using ha.clog_real hs
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((continuous_horizontal_reciprocal rho t ht).intervalIntegrable a b)

lemma integral_vertical_reciprocal_right (rho : ℂ) (r c d : ℝ)
    (hr : rho.re < r) :
    I * (∫ y : ℝ in c..d, 1 / ((r : ℂ) + (y : ℂ) * I - rho)) =
      Complex.log ((r : ℂ) + (d : ℂ) * I - rho) -
      Complex.log ((r : ℂ) + (c : ℂ) * I - rho) := by
  have hd (y : ℝ) : HasDerivAt
      (fun y : ℝ => Complex.log ((r : ℂ) + (y : ℂ) * I - rho))
      (I * (1 / ((r : ℂ) + (y : ℂ) * I - rho))) y := by
    have hs : (r : ℂ) + (y : ℂ) * I - rho ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      simpa using sub_pos.mpr hr
    have ha := ((((hasDerivAt_id y).ofReal_comp).mul_const I).const_add (r : ℂ)).sub_const rho
    simpa [div_eq_mul_inv] using ha.clog_real hs
  have hc : Continuous (fun y : ℝ => I * (1 / ((r : ℂ) + (y : ℂ) * I - rho))) :=
    continuous_const.mul (continuous_vertical_reciprocal rho r (ne_of_gt hr))
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)
    (hc.intervalIntegrable c d)
  simpa only [intervalIntegral.integral_const_mul] using hh

lemma integral_vertical_reciprocal_left (rho : ℂ) (r c d : ℝ)
    (hr : r < rho.re) :
    I * (∫ y : ℝ in c..d, 1 / ((r : ℂ) + (y : ℂ) * I - rho)) =
      Complex.log (rho - ((r : ℂ) + (d : ℂ) * I)) -
      Complex.log (rho - ((r : ℂ) + (c : ℂ) * I)) := by
  have hd (y : ℝ) : HasDerivAt
      (fun y : ℝ => Complex.log (rho - ((r : ℂ) + (y : ℂ) * I)))
      (I * (1 / ((r : ℂ) + (y : ℂ) * I - rho))) y := by
    have hs : rho - ((r : ℂ) + (y : ℂ) * I) ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      simpa using sub_pos.mpr hr
    have ha := ((((hasDerivAt_id y).ofReal_comp).mul_const I).const_add (r : ℂ)).const_sub rho
    have hh : HasDerivAt
        (fun y : ℝ => Complex.log (rho - ((r : ℂ) + (y : ℂ) * I)))
        ((-I) / (rho - ((r : ℂ) + (y : ℂ) * I))) y := by
      simpa using ha.clog_real hs
    have he : rho - ((r : ℂ) + (y : ℂ) * I) =
        -((r : ℂ) + (y : ℂ) * I - rho) := by ring
    have hscalar : (-I) / (rho - ((r : ℂ) + (y : ℂ) * I)) =
        I * (1 / ((r : ℂ) + (y : ℂ) * I - rho)) := by
      rw [he, neg_div_neg_eq]
      simp only [div_eq_mul_inv, one_mul]
    rw [hscalar] at hh
    exact hh
  have hc : Continuous (fun y : ℝ => I * (1 / ((r : ℂ) + (y : ℂ) * I - rho))) :=
    continuous_const.mul (continuous_vertical_reciprocal rho r (ne_of_lt hr))
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)
    (hc.intervalIntegrable c d)
  simpa only [intervalIntegral.integral_const_mul] using hh

theorem rectangle_reciprocal_integrable (a b c d : ℝ) (rho : ℂ)
    (ha : a < rho.re) (hb : rho.re < b) (hc : c < rho.im) (hd : rho.im < d) :
    IntervalIntegrable (fun x : ℝ => 1 / ((x : ℂ) + (c : ℂ) * I - rho)) volume a b ∧
    IntervalIntegrable (fun x : ℝ => 1 / ((x : ℂ) + (d : ℂ) * I - rho)) volume a b ∧
    IntervalIntegrable (fun y : ℝ => 1 / ((b : ℂ) + (y : ℂ) * I - rho)) volume c d ∧
    IntervalIntegrable (fun y : ℝ => 1 / ((a : ℂ) + (y : ℂ) * I - rho)) volume c d := by
  exact ⟨(continuous_horizontal_reciprocal rho c (ne_of_lt hc)).intervalIntegrable a b,
    (continuous_horizontal_reciprocal rho d (ne_of_gt hd)).intervalIntegrable a b,
    (continuous_vertical_reciprocal rho b (ne_of_gt hb)).intervalIntegrable c d,
    (continuous_vertical_reciprocal rho a (ne_of_lt ha)).intervalIntegrable c d⟩

theorem rectangle_reciprocal (a b c d : ℝ) (rho : ℂ)
    (ha : a < rho.re) (hb : rho.re < b) (hc : c < rho.im) (hd : rho.im < d) :
    (∫ x : ℝ in a..b, 1 / ((x : ℂ) + (c : ℂ) * I - rho)) -
      (∫ x : ℝ in a..b, 1 / ((x : ℂ) + (d : ℂ) * I - rho)) +
      I * (∫ y : ℝ in c..d, 1 / ((b : ℂ) + (y : ℂ) * I - rho)) -
      I * (∫ y : ℝ in c..d, 1 / ((a : ℂ) + (y : ℂ) * I - rho)) =
      2 * (Real.pi : ℂ) * I := by
  rw [integral_horizontal_reciprocal rho c a b (ne_of_lt hc),
    integral_horizontal_reciprocal rho d a b (ne_of_gt hd),
    integral_vertical_reciprocal_right rho b c d hb,
    integral_vertical_reciprocal_left rho a c d ha]
  have ht : 0 < ((a : ℂ) + (d : ℂ) * I - rho).im := by
    simpa using sub_pos.mpr hd
  have hl : ((a : ℂ) + (c : ℂ) * I - rho).im < 0 := by
    simpa using sub_neg.mpr hc
  have hut := log_sub_log_neg_of_im_pos ((a : ℂ) + (d : ℂ) * I - rho) ht
  have hlb := log_sub_log_neg_of_im_neg ((a : ℂ) + (c : ℂ) * I - rho) hl
  rw [show rho - ((a : ℂ) + (d : ℂ) * I) =
      -((a : ℂ) + (d : ℂ) * I - rho) by ring,
    show rho - ((a : ℂ) + (c : ℂ) * I) =
      -((a : ℂ) + (c : ℂ) * I - rho) by ring]
  linear_combination hut - hlb

end RiemannVonMangoldt.RectKernel

end P2MFinalSource001

/- Source module: RectangleBoundaryV2
   Original SHA256: a7e4e0292bd5210486d93a064473f3123a54ac5014f86386baa8caa1b2e98413 -/
section P2MFinalSource002

/-!
Counterclockwise rectangle boundary operator and finite principal-part sums.
Linearity of finite sums is justified by all four actual edge integrabilities.
The reciprocal-kernel value is imported from the separately checked source.
-/

set_option autoImplicit false

open Complex MeasureTheory
open scoped Interval BigOperators

namespace RiemannVonMangoldt.RectKernel

noncomputable def boundary (a b c d : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in a..b, f ((x : ℂ) + (c : ℂ) * I)) -
    (∫ x : ℝ in a..b, f ((x : ℂ) + (d : ℂ) * I)) +
    I * (∫ y : ℝ in c..d, f ((b : ℂ) + (y : ℂ) * I)) -
    I * (∫ y : ℝ in c..d, f ((a : ℂ) + (y : ℂ) * I))

def BoundaryIntegrable (a b c d : ℝ) (f : ℂ → ℂ) : Prop :=
  IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (c : ℂ) * I)) volume a b ∧
  IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * I)) volume a b ∧
  IntervalIntegrable (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * I)) volume c d ∧
  IntervalIntegrable (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * I)) volume c d

lemma BoundaryIntegrable.add {a b c d : ℝ} {f g : ℂ → ℂ}
    (hf : BoundaryIntegrable a b c d f) (hg : BoundaryIntegrable a b c d g) :
    BoundaryIntegrable a b c d (fun z => f z + g z) :=
  ⟨hf.1.add hg.1, hf.2.1.add hg.2.1,
    hf.2.2.1.add hg.2.2.1, hf.2.2.2.add hg.2.2.2⟩

lemma BoundaryIntegrable.sub {a b c d : ℝ} {f g : ℂ → ℂ}
    (hf : BoundaryIntegrable a b c d f) (hg : BoundaryIntegrable a b c d g) :
    BoundaryIntegrable a b c d (fun z => f z - g z) :=
  ⟨hf.1.sub hg.1, hf.2.1.sub hg.2.1,
    hf.2.2.1.sub hg.2.2.1, hf.2.2.2.sub hg.2.2.2⟩

lemma BoundaryIntegrable.const_mul {a b c d : ℝ} {f : ℂ → ℂ}
    (hf : BoundaryIntegrable a b c d f) (k : ℂ) :
    BoundaryIntegrable a b c d (fun z => k * f z) :=
  ⟨hf.1.const_mul k, hf.2.1.const_mul k,
    hf.2.2.1.const_mul k, hf.2.2.2.const_mul k⟩

lemma BoundaryIntegrable.finset_sum {ι : Type*} {a b c d : ℝ}
    (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, BoundaryIntegrable a b c d (f i)) :
    BoundaryIntegrable a b c d (fun z => ∑ i ∈ s, f i z) := by
  have hsum (u v : ℝ) (g : ι → ℝ → ℂ)
      (hg : ∀ i ∈ s, IntervalIntegrable (g i) volume u v) :
      IntervalIntegrable (fun x => ∑ i ∈ s, g i x) volume u v := by
    have he : (∑ i ∈ s, g i) = (fun x => ∑ i ∈ s, g i x) := by
      funext x
      simp only [Finset.sum_apply]
    rw [← he]
    exact IntervalIntegrable.sum s hg
  exact ⟨hsum a b (fun i x => f i ((x : ℂ) + (c : ℂ) * I))
      (fun i hi => (hf i hi).1),
    hsum a b (fun i x => f i ((x : ℂ) + (d : ℂ) * I))
      (fun i hi => (hf i hi).2.1),
    hsum c d (fun i y => f i ((b : ℂ) + (y : ℂ) * I))
      (fun i hi => (hf i hi).2.2.1),
    hsum c d (fun i y => f i ((a : ℂ) + (y : ℂ) * I))
      (fun i hi => (hf i hi).2.2.2)⟩

lemma boundary_add (a b c d : ℝ) (f g : ℂ → ℂ)
    (hf : BoundaryIntegrable a b c d f) (hg : BoundaryIntegrable a b c d g) :
    boundary a b c d (fun z => f z + g z) =
      boundary a b c d f + boundary a b c d g := by
  unfold boundary
  rw [intervalIntegral.integral_add hf.1 hg.1,
    intervalIntegral.integral_add hf.2.1 hg.2.1,
    intervalIntegral.integral_add hf.2.2.1 hg.2.2.1,
    intervalIntegral.integral_add hf.2.2.2 hg.2.2.2]
  ring

lemma boundary_sub (a b c d : ℝ) (f g : ℂ → ℂ)
    (hf : BoundaryIntegrable a b c d f) (hg : BoundaryIntegrable a b c d g) :
    boundary a b c d (fun z => f z - g z) =
      boundary a b c d f - boundary a b c d g := by
  unfold boundary
  rw [intervalIntegral.integral_sub hf.1 hg.1,
    intervalIntegral.integral_sub hf.2.1 hg.2.1,
    intervalIntegral.integral_sub hf.2.2.1 hg.2.2.1,
    intervalIntegral.integral_sub hf.2.2.2 hg.2.2.2]
  ring

lemma boundary_const_mul (a b c d : ℝ) (k : ℂ) (f : ℂ → ℂ) :
    boundary a b c d (fun z => k * f z) = k * boundary a b c d f := by
  unfold boundary
  simp only [intervalIntegral.integral_const_mul]
  ring

lemma boundary_finset_sum {ι : Type*} (a b c d : ℝ)
    (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, BoundaryIntegrable a b c d (f i)) :
    boundary a b c d (fun z => ∑ i ∈ s, f i z) =
      ∑ i ∈ s, boundary a b c d (f i) := by
  unfold boundary
  rw [intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).1),
    intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).2.1),
    intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).2.2.1),
    intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).2.2.2)]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

lemma boundary_reciprocal (a b c d : ℝ) (rho : ℂ)
    (ha : a < rho.re) (hb : rho.re < b) (hc : c < rho.im) (hd : rho.im < d) :
    boundary a b c d (fun z => 1 / (z - rho)) = 2 * (Real.pi : ℂ) * I :=
  rectangle_reciprocal a b c d rho ha hb hc hd

lemma boundaryIntegrable_reciprocal (a b c d : ℝ) (rho : ℂ)
    (ha : a < rho.re) (hb : rho.re < b) (hc : c < rho.im) (hd : rho.im < d) :
    BoundaryIntegrable a b c d (fun z => 1 / (z - rho)) :=
  rectangle_reciprocal_integrable a b c d rho ha hb hc hd

theorem finite_principal_parts_integrable {ι : Type*} (a b c d : ℝ)
    (s : Finset ι) (rho weight : ι → ℂ)
    (hinterior : ∀ i ∈ s,
      a < (rho i).re ∧ (rho i).re < b ∧ c < (rho i).im ∧ (rho i).im < d) :
    BoundaryIntegrable a b c d (fun z => ∑ i ∈ s, weight i / (z - rho i)) := by
  have hf (i : ι) (hi : i ∈ s) :
      BoundaryIntegrable a b c d (fun z => weight i * (1 / (z - rho i))) := by
    rcases hinterior i hi with ⟨ha, hb, hc, hd⟩
    exact (boundaryIntegrable_reciprocal a b c d (rho i) ha hb hc hd).const_mul (weight i)
  simpa only [div_eq_mul_inv, one_div, one_mul] using
    BoundaryIntegrable.finset_sum s (fun i z => weight i * (1 / (z - rho i))) hf

theorem boundary_finite_principal_parts {ι : Type*} (a b c d : ℝ)
    (s : Finset ι) (rho weight : ι → ℂ)
    (hinterior : ∀ i ∈ s,
      a < (rho i).re ∧ (rho i).re < b ∧ c < (rho i).im ∧ (rho i).im < d) :
    boundary a b c d (fun z => ∑ i ∈ s, weight i / (z - rho i)) =
      (2 * (Real.pi : ℂ) * I) * ∑ i ∈ s, weight i := by
  have hf (i : ι) (hi : i ∈ s) :
      BoundaryIntegrable a b c d (fun z => weight i * (1 / (z - rho i))) := by
    rcases hinterior i hi with ⟨ha, hb, hc, hd⟩
    exact (boundaryIntegrable_reciprocal a b c d (rho i) ha hb hc hd).const_mul (weight i)
  have hs := boundary_finset_sum a b c d s
    (fun i z => weight i * (1 / (z - rho i))) hf
  have he :
      (∑ i ∈ s, boundary a b c d (fun z => weight i * (1 / (z - rho i)))) =
        (2 * (Real.pi : ℂ) * I) * ∑ i ∈ s, weight i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rcases hinterior i hi with ⟨ha, hb, hc, hd⟩
    rw [boundary_const_mul,
      boundary_reciprocal a b c d (rho i) ha hb hc hd]
    ring
  simpa only [div_eq_mul_inv, one_div, one_mul] using hs.trans he

end RiemannVonMangoldt.RectKernel

end P2MFinalSource002

/- Source module: RectangleCauchyAssemblyV1
   Original SHA256: 8d47c0846b0d9b23f42de18e46b84f69ce4d034a3a9544f7b873b45e326cba60 -/
section P2MFinalSource003

/-!
Small assembly layer for the existing four-edge operator. This is local
support, not an originality or public-admission claim: a stronger accepted
same-environment argument-principle theorem has been located separately.
-/

set_option autoImplicit false

open Complex MeasureTheory Set
open scoped Interval BigOperators

namespace RiemannVonMangoldt.RectKernel

def BoundaryEq (a b c d : ℝ) (f g : ℂ → ℂ) : Prop :=
  EqOn (fun x : ℝ => f ((x : ℂ) + (c : ℂ) * I))
    (fun x : ℝ => g ((x : ℂ) + (c : ℂ) * I)) (uIcc a b) ∧
  EqOn (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * I))
    (fun x : ℝ => g ((x : ℂ) + (d : ℂ) * I)) (uIcc a b) ∧
  EqOn (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * I))
    (fun y : ℝ => g ((b : ℂ) + (y : ℂ) * I)) (uIcc c d) ∧
  EqOn (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * I))
    (fun y : ℝ => g ((a : ℂ) + (y : ℂ) * I)) (uIcc c d)

lemma boundary_congr (a b c d : ℝ) (f g : ℂ → ℂ)
    (h : BoundaryEq a b c d f g) : boundary a b c d f = boundary a b c d g := by
  unfold boundary
  rw [intervalIntegral.integral_congr h.1,
    intervalIntegral.integral_congr h.2.1,
    intervalIntegral.integral_congr h.2.2.1,
    intervalIntegral.integral_congr h.2.2.2]

lemma boundary_eq_zero_of_analyticOnNhd (a b c d : ℝ) (G : ℂ → ℂ)
    (hG : AnalyticOnNhd ℂ G (uIcc a b ×ℂ uIcc c d)) :
    boundary a b c d G = 0 := by
  have hd : DifferentiableOn ℂ G
      (uIcc (((a : ℂ) + (c : ℂ) * I).re) (((b : ℂ) + (d : ℂ) * I).re) ×ℂ
        uIcc (((a : ℂ) + (c : ℂ) * I).im) (((b : ℂ) + (d : ℂ) * I).im)) := by
    simpa using hG.differentiableOn
  simpa [boundary, smul_eq_mul] using
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn G
      ((a : ℂ) + (c : ℂ) * I) ((b : ℂ) + (d : ℂ) * I) hd

theorem boundary_of_principal_part_extension {ι : Type*}
    (a b c d : ℝ) (F G : ℂ → ℂ) (s : Finset ι) (rho weight : ι → ℂ)
    (hinterior : ∀ i ∈ s,
      a < (rho i).re ∧ (rho i).re < b ∧ c < (rho i).im ∧ (rho i).im < d)
    (hF : BoundaryIntegrable a b c d F)
    (hG : AnalyticOnNhd ℂ G (uIcc a b ×ℂ uIcc c d))
    (hboundary : BoundaryEq a b c d G
      (fun z => F z - ∑ i ∈ s, weight i / (z - rho i))) :
    boundary a b c d F = (2 * (Real.pi : ℂ) * I) * ∑ i ∈ s, weight i := by
  let P : ℂ → ℂ := fun z => ∑ i ∈ s, weight i / (z - rho i)
  have hP : BoundaryIntegrable a b c d P :=
    finite_principal_parts_integrable a b c d s rho weight hinterior
  have hz : boundary a b c d F - boundary a b c d P = 0 := by
    calc
      boundary a b c d F - boundary a b c d P =
          boundary a b c d (fun z => F z - P z) :=
        (boundary_sub a b c d F P hF hP).symm
      _ = boundary a b c d G :=
        (boundary_congr a b c d G (fun z => F z - P z) hboundary).symm
      _ = 0 := boundary_eq_zero_of_analyticOnNhd a b c d G hG
  exact (sub_eq_zero.mp hz).trans
    (boundary_finite_principal_parts a b c d s rho weight hinterior)

end RiemannVonMangoldt.RectKernel

end P2MFinalSource003

/- Source module: RectangleZeroSetV1
   Original SHA256: 6252866ef3a234324a793b6b3727a148e41335f7b916bc232b4a11f1bcba640f -/
section P2MFinalSource004

/-!
# Finitely many zeros in a zero-free-boundary rectangle

The domain is the actual closed rectangle `Icc a b ×ℂ Icc c d`.
Boundary nonvanishing is stated on its difference with the corresponding open
rectangle. A nonzero bottom-left corner rules out infinite analytic order on
the whole connected rectangle. The zeros are then finite by compactness and
the genuine analytic isolated-zero theorem.
-/

noncomputable section

open Complex Filter Set
open scoped Topology

namespace RiemannVonMangoldt.RectangleZeros

/-- The closed rectangle is connected; no analyticity assumption is involved. -/
lemma closed_rectangle_isPreconnected (a b c d : ℝ) :
    IsPreconnected (Icc a b ×ℂ Icc c d) := by
  have hconv : Convex ℝ (Icc a b ×ℂ Icc c d) :=
    ((convex_halfSpace_re_ge a).inter (convex_halfSpace_re_le b)).inter
      ((convex_halfSpace_im_ge c).inter (convex_halfSpace_im_le d))
  exact hconv.isPreconnected

/-- Nonvanishing on the boundary of a nondegenerate closed rectangle gives
finite analytic order everywhere, a finite zero set, and strict interior
membership for every zero. -/
theorem rectangle_zero_set_finite_and_orders
    (a b c d : ℝ) (hab : a < b) (hcd : c < d) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Icc a b ×ℂ Icc c d))
    (hboundary : ∀ z ∈ (Icc a b ×ℂ Icc c d) \ (Ioo a b ×ℂ Ioo c d), f z ≠ 0) :
    {z : ℂ | z ∈ (Icc a b ×ℂ Icc c d) ∧ f z = 0}.Finite ∧
      (∀ z ∈ (Icc a b ×ℂ Icc c d), analyticOrderAt f z ≠ ⊤) ∧
      (∀ z ∈ (Icc a b ×ℂ Icc c d), f z = 0 → z ∈ (Ioo a b ×ℂ Ioo c d)) := by
  let corner : ℂ := (a : ℂ) + (c : ℂ) * I
  have hcorner : corner ∈ (Icc a b ×ℂ Icc c d) := by
    simp [corner, mem_reProdIm, hab.le, hcd.le]
  have hcorner_not_open : corner ∉ (Ioo a b ×ℂ Ioo c d) := by
    simp [corner, mem_reProdIm]
  have hcorner_ne : f corner ≠ 0 := hboundary corner ⟨hcorner, hcorner_not_open⟩
  have hpre : IsPreconnected (Icc a b ×ℂ Icc c d) :=
    closed_rectangle_isPreconnected a b c d
  have hconnected : IsConnected (Icc a b ×ℂ Icc c d) :=
    ⟨⟨corner, hcorner⟩, hpre⟩
  have hcompact : IsCompact (Icc a b ×ℂ Icc c d) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hcodiscrete : f ⁻¹' ({0} : Set ℂ)ᶜ ∈ codiscreteWithin (Icc a b ×ℂ Icc c d) :=
    hf.preimage_zero_mem_codiscreteWithin hcorner_ne hcorner hconnected
  have hfinite_diff := hcompact.finite_sdiff_of_mem_codiscreteWithin hcodiscrete
  have hfinite : {z : ℂ | z ∈ (Icc a b ×ℂ Icc c d) ∧ f z = 0}.Finite := by
    apply hfinite_diff.subset
    intro z hz
    exact ⟨hz.1, fun h => h hz.2⟩
  have hcorner_order : analyticOrderAt f corner ≠ ⊤ := by
    rw [(hf corner hcorner).analyticOrderAt_eq_zero.mpr hcorner_ne]
    exact ENat.zero_ne_top
  refine ⟨hfinite, ?_, ?_⟩
  · intro z hz
    exact hf.analyticOrderAt_ne_top_of_isPreconnected hpre hcorner hz hcorner_order
  · intro z hz hfz
    by_contra hnot
    exact hboundary z ⟨hz, hnot⟩ hfz

/-- A finite set representing exactly the original function's rectangle zeros,
with every member strictly interior and every rectangle point of finite order.
This is the finite-set input needed for the principal-part construction. -/
theorem exists_finset_rectangle_zeros
    (a b c d : ℝ) (hab : a < b) (hcd : c < d) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Icc a b ×ℂ Icc c d))
    (hboundary : ∀ z ∈ (Icc a b ×ℂ Icc c d) \ (Ioo a b ×ℂ Ioo c d), f z ≠ 0) :
    ∃ S : Finset ℂ,
      (∀ z, z ∈ S ↔ z ∈ (Icc a b ×ℂ Icc c d) ∧ f z = 0) ∧
      (∀ z ∈ S, z ∈ (Ioo a b ×ℂ Ioo c d)) ∧
      (∀ z ∈ (Icc a b ×ℂ Icc c d), analyticOrderAt f z ≠ ⊤) := by
  classical
  obtain ⟨hfinite, horders, hinterior⟩ :=
    rectangle_zero_set_finite_and_orders a b c d hab hcd hf hboundary
  let S : Finset ℂ := hfinite.toFinset
  have hmem (z : ℂ) : z ∈ S ↔ z ∈ (Icc a b ×ℂ Icc c d) ∧ f z = 0 := by
    simp [S]
  refine ⟨S, hmem, ?_, horders⟩
  intro z hz
  obtain ⟨hzR, hfz⟩ := (hmem z).mp hz
  exact hinterior z hzR hfz


end RiemannVonMangoldt.RectangleZeros
end
end P2MFinalSource004

/- Source module: LogDerivPrincipalPartV2
   Original SHA256: 96e7f492f9c04dc0fa5d6fe6199d01941558c9321e1473774ef580b63fa38156 -/
section P2MFinalSource005

/-!
# Removing the genuine principal part of a logarithmic derivative

Source candidate for the pinned Mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474`.

The multiplicity is the actual analytic order, and its finiteness is an explicit
hypothesis. The extension is constructed from the nonvanishing analytic factor
in Mathlib's local factorization theorem. No contour identity is assumed.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace RiemannVonMangoldt.PrincipalPart

/-- The logarithmic derivative of a centered natural power. -/
lemma logDeriv_centered_pow (rho z : ℂ) (m : ℕ) :
    logDeriv (fun w : ℂ => (w - rho) ^ m) z = (m : ℂ) / (z - rho) := by
  rw [logDeriv_fun_pow (f := fun w : ℂ => w - rho) (x := z) (by fun_prop) m]
  simp [logDeriv_apply, mul_one_div, div_eq_mul_inv]

/-- At a point of exact finite analytic order `m`, removing `m/(z-rho)` from
the logarithmic derivative leaves the germ of an actual analytic function. -/
theorem exists_analytic_logDeriv_sub_principal_part
    {f : ℂ → ℂ} {rho : ℂ} {m : ℕ}
    (hf : AnalyticAt ℂ f rho) (hm : analyticOrderAt f rho = (m : ℕ∞)) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H rho ∧
      (fun z => logDeriv f z - (m : ℂ) / (z - rho)) =ᶠ[𝓝[≠] rho] H := by
  obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_eq_natCast.mp hm
  have hfactor : f =ᶠ[𝓝 rho] fun z => (z - rho) ^ m * g z := by
    filter_upwards [hfg] with z hz
    simpa only [smul_eq_mul] using hz
  have hlog := logDeriv_congr_nhds hfactor
  have hg_ne : ∀ᶠ z in 𝓝 rho, g z ≠ 0 := hg.continuousAt.eventually_ne hg0
  refine ⟨logDeriv g, hg.deriv.div hg hg0, ?_⟩
  filter_upwards [hlog.filter_mono nhdsWithin_le_nhds,
    hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    hg_ne.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with z hz hgz hgnz hzr
  have hsub : z - rho ≠ 0 := sub_ne_zero.mpr hzr
  rw [hz, logDeriv_mul (f := fun w : ℂ => (w - rho) ^ m) (g := g)
    z (pow_ne_zero m hsub) hgnz (by fun_prop) hgz.differentiableAt,
    logDeriv_centered_pow]
  exact add_sub_cancel_left _ _

/-- The coefficient is the genuine natural analytic order; infinite order
is explicitly excluded rather than erased by `ENat.toNat`. -/
theorem exists_analytic_logDeriv_sub_analyticOrderNatAt
    {f : ℂ → ℂ} {rho : ℂ}
    (hf : AnalyticAt ℂ f rho) (hfinite : analyticOrderAt f rho ≠ ⊤) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H rho ∧
      (fun z => logDeriv f z - (analyticOrderNatAt f rho : ℂ) / (z - rho))
        =ᶠ[𝓝[≠] rho] H :=
  exists_analytic_logDeriv_sub_principal_part hf
    (Nat.cast_analyticOrderNatAt hfinite).symm

/-- Choosing the extension's value at the center gives an analytic corrected
function that agrees with the original difference at every other point. -/
theorem exists_analytic_logDeriv_sub_principal_part_update
    {f : ℂ → ℂ} {rho : ℂ} {m : ℕ}
    (hf : AnalyticAt ℂ f rho) (hm : analyticOrderAt f rho = (m : ℕ∞)) :
    ∃ c : ℂ, AnalyticAt ℂ
      (fun z => if z = rho then c else logDeriv f z - (m : ℂ) / (z - rho)) rho := by
  obtain ⟨H, hH, heq⟩ := exists_analytic_logDeriv_sub_principal_part hf hm
  refine ⟨H rho, hH.congr ?_⟩
  have heq' := eventually_nhdsWithin_iff.mp heq
  filter_upwards [heq'] with z hz
  by_cases hzr : z = rho
  · simp [hzr]
  · simp only [if_neg hzr]
    exact (hz hzr).symm


end RiemannVonMangoldt.PrincipalPart
end
end P2MFinalSource005

/- Source module: FinitePrincipalPartsV1
   Original SHA256: 1887d6df6d8a51e588942be7523f86fac03833e9c807cd1b3c0533405cc0bd86 -/
section P2MFinalSource006

/-!
# Removing all genuine logarithmic principal parts in a finite set

The analytic orders are those of the original function. Finiteness of each
order and coverage of every zero in the domain are explicit hypotheses.
This constructs a function analytic across the finite zero set, rather than
asserting that the totalized raw logarithmic derivative is continuous there.
-/

noncomputable section

open Filter Set
open scoped Topology BigOperators

namespace RiemannVonMangoldt.PrincipalPart

/-- Finitely many analytic punctured germs can be filled by choosing their
actual limiting values. The resulting function agrees with the original
function at every point outside the finite exceptional set. -/
theorem exists_analyticOnNhd_extension_finset
    (S : Finset ℂ) (U : Set ℂ) (F : ℂ → ℂ)
    (haway : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ F z)
    (hlocal : ∀ rho ∈ S, ∃ H : ℂ → ℂ,
      AnalyticAt ℂ H rho ∧ F =ᶠ[𝓝[≠] rho] H) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G U ∧ ∀ z ∉ S, G z = F z := by
  classical
  induction S using Finset.induction_on generalizing F with
  | empty =>
      refine ⟨F, ?_, fun _ _ => rfl⟩
      intro z hz
      exact haway z hz (by simp)
  | @insert a S ha ih =>
      obtain ⟨H, hH, hFH⟩ := hlocal a (by simp)
      let F₁ : ℂ → ℂ := fun z => if z = a then H a else F z
      have hF₁a : AnalyticAt ℂ F₁ a := by
        apply hH.congr
        have hFH' := eventually_nhdsWithin_iff.mp hFH
        filter_upwards [hFH'] with z hz
        by_cases hza : z = a
        · simp [F₁, hza]
        · simp only [F₁, if_neg hza]
          exact (hz hza).symm
      have hF₁eq : ∀ z : ℂ, z ≠ a → F₁ =ᶠ[𝓝 z] F := by
        intro z hza
        filter_upwards [eventually_ne_nhds hza] with w hw
        simp [F₁, hw]
      have haway₁ : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ F₁ z := by
        intro z hz hzS
        by_cases hza : z = a
        · simpa only [hza] using hF₁a
        · exact (haway z hz (by simp [hza, hzS])).congr (hF₁eq z hza).symm
      have hlocal₁ : ∀ rho ∈ S, ∃ K : ℂ → ℂ,
          AnalyticAt ℂ K rho ∧ F₁ =ᶠ[𝓝[≠] rho] K := by
        intro rho hrho
        obtain ⟨K, hK, hFK⟩ := hlocal rho (by simp [hrho])
        have hrhoa : rho ≠ a := by
          intro h
          subst rho
          exact ha hrho
        exact ⟨K, hK,
          ((hF₁eq rho hrhoa).filter_mono nhdsWithin_le_nhds).trans hFK⟩
      obtain ⟨G, hG, hGF₁⟩ := ih F₁ haway₁ hlocal₁
      refine ⟨G, hG, ?_⟩
      intro z hz
      have hz' : z ≠ a ∧ z ∉ S := by
        simpa only [Finset.mem_insert, not_or] using hz
      simpa only [F₁, if_neg hz'.1] using hGF₁ z hz'.2

/-- Subtracting every finite-order zero's genuine principal part produces a
function with an analytic extension across all those zeros. Coverage of zeros
is required on the whole domain `U`, including its boundary when present. -/
theorem exists_analyticOnNhd_logDeriv_sub_finite_principal_parts
    {f : ℂ → ℂ} {U : Set ℂ} (S : Finset ℂ)
    (hf : AnalyticOnNhd ℂ f U)
    (hS : ∀ rho ∈ S, rho ∈ U)
    (hfinite : ∀ rho ∈ S, analyticOrderAt f rho ≠ ⊤)
    (hzeros : ∀ z ∈ U, f z = 0 → z ∈ S) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G U ∧
      ∀ z ∉ S, G z = logDeriv f z -
        ∑ rho ∈ S, (analyticOrderNatAt f rho : ℂ) / (z - rho) := by
  classical
  apply exists_analyticOnNhd_extension_finset S U
    (fun z => logDeriv f z -
      ∑ rho ∈ S, (analyticOrderNatAt f rho : ℂ) / (z - rho))
  · intro z hz hzS
    have hfz : f z ≠ 0 := fun h => hzS (hzeros z hz h)
    have hlog : AnalyticAt ℂ (logDeriv f) z := (hf z hz).deriv.div (hf z hz) hfz
    have hsum : AnalyticAt ℂ
        (fun w => ∑ rho ∈ S, (analyticOrderNatAt f rho : ℂ) / (w - rho)) z := by
      apply Finset.analyticAt_fun_sum S
      intro rho hrho
      have hzr : z - rho ≠ 0 := by
        apply sub_ne_zero.mpr
        intro h
        subst z
        exact hzS hrho
      exact analyticAt_const.div (analyticAt_id.sub analyticAt_const) hzr
    exact hlog.sub hsum
  · intro rho hrho
    obtain ⟨H, hH, hEq⟩ :=
      exists_analytic_logDeriv_sub_analyticOrderNatAt (hf rho (hS rho hrho))
        (hfinite rho hrho)
    let J : ℂ → ℂ := fun z =>
      ∑ sigma ∈ S.erase rho, (analyticOrderNatAt f sigma : ℂ) / (z - sigma)
    have hJ : AnalyticAt ℂ J rho := by
      apply Finset.analyticAt_fun_sum (S.erase rho)
      intro sigma hsigma
      have hrs : rho - sigma ≠ 0 :=
        sub_ne_zero.mpr (Finset.mem_erase.mp hsigma).1.symm
      exact analyticAt_const.div (analyticAt_id.sub analyticAt_const) hrs
    refine ⟨fun z => H z - J z, hH.sub hJ, ?_⟩
    filter_upwards [hEq] with z hz
    have hsum : (∑ sigma ∈ S, (analyticOrderNatAt f sigma : ℂ) / (z - sigma)) =
        (analyticOrderNatAt f rho : ℂ) / (z - rho) + J z := by
      exact (Finset.add_sum_erase S
        (fun sigma => (analyticOrderNatAt f sigma : ℂ) / (z - sigma)) hrho).symm
    rw [hsum, sub_add_eq_sub_sub, hz]


end RiemannVonMangoldt.PrincipalPart
end
end P2MFinalSource006

/- Source module: AnalyticRectangleCountV2
   Original SHA256: 33eba4285ad02fa08e9c2138d1b60fb251139fc433904f3f046e7852dbcada0f -/
section P2MFinalSource007

/-!
Complete the already-in-flight unweighted analytic rectangle assembly.
The zero set and finite analytic orders are derived from actual analyticity,
compactness, connectedness and boundary nonvanishing. The logarithmic derivative
is made analytic only after its genuine finite principal parts are removed.

This is internal checked-support work; a stronger previously accepted general
argument principle exists and must be credited. No novelty is asserted.
-/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set
open scoped Interval BigOperators

namespace RiemannVonMangoldt.RectKernel

lemma boundaryIntegrable_of_continuousOn (a b c d : ℝ) (G : ℂ → ℂ)
    (hG : ContinuousOn G (uIcc a b ×ℂ uIcc c d)) :
    BoundaryIntegrable a b c d G := by
  have hbottom : MapsTo (fun x : ℝ => (x : ℂ) + (c : ℂ) * I)
      (uIcc a b) (uIcc a b ×ℂ uIcc c d) := by
    intro x hx
    change ((x : ℂ) + (c : ℂ) * I).re ∈ uIcc a b ∧
      ((x : ℂ) + (c : ℂ) * I).im ∈ uIcc c d
    simpa using And.intro hx (left_mem_uIcc : c ∈ uIcc c d)
  have htop : MapsTo (fun x : ℝ => (x : ℂ) + (d : ℂ) * I)
      (uIcc a b) (uIcc a b ×ℂ uIcc c d) := by
    intro x hx
    change ((x : ℂ) + (d : ℂ) * I).re ∈ uIcc a b ∧
      ((x : ℂ) + (d : ℂ) * I).im ∈ uIcc c d
    simpa using And.intro hx (right_mem_uIcc : d ∈ uIcc c d)
  have hright : MapsTo (fun y : ℝ => (b : ℂ) + (y : ℂ) * I)
      (uIcc c d) (uIcc a b ×ℂ uIcc c d) := by
    intro y hy
    change ((b : ℂ) + (y : ℂ) * I).re ∈ uIcc a b ∧
      ((b : ℂ) + (y : ℂ) * I).im ∈ uIcc c d
    simpa using And.intro (right_mem_uIcc : b ∈ uIcc a b) hy
  have hleft : MapsTo (fun y : ℝ => (a : ℂ) + (y : ℂ) * I)
      (uIcc c d) (uIcc a b ×ℂ uIcc c d) := by
    intro y hy
    change ((a : ℂ) + (y : ℂ) * I).re ∈ uIcc a b ∧
      ((a : ℂ) + (y : ℂ) * I).im ∈ uIcc c d
    simpa using And.intro (left_mem_uIcc : a ∈ uIcc a b) hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hG.comp (by fun_prop) hbottom).intervalIntegrable
  · exact (hG.comp (by fun_prop) htop).intervalIntegrable
  · exact (hG.comp (by fun_prop) hright).intervalIntegrable
  · exact (hG.comp (by fun_prop) hleft).intervalIntegrable

lemma boundaryIntegrable_congr (a b c d : ℝ) (F G : ℂ → ℂ)
    (hF : BoundaryIntegrable a b c d F) (hEq : BoundaryEq a b c d F G) :
    BoundaryIntegrable a b c d G := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (intervalIntegrable_congr
      (fun x hx => hEq.1 (uIoc_subset_uIcc hx))).mp hF.1
  · exact (intervalIntegrable_congr
      (fun x hx => hEq.2.1 (uIoc_subset_uIcc hx))).mp hF.2.1
  · exact (intervalIntegrable_congr
      (fun y hy => hEq.2.2.1 (uIoc_subset_uIcc hy))).mp hF.2.2.1
  · exact (intervalIntegrable_congr
      (fun y hy => hEq.2.2.2 (uIoc_subset_uIcc hy))).mp hF.2.2.2

/-- The actual logarithmic derivative integrates to the multiplicity-weighted
sum over precisely all zeros in a nondegenerate closed rectangle. Both the
finite zero set and the finiteness of its genuine analytic orders are derived.
The four edge integrals are proved integrable as part of the conclusion. -/
theorem analytic_rectangle_logDeriv_count
    (a b c d : ℝ) (hab : a < b) (hcd : c < d) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Icc a b ×ℂ Icc c d))
    (hboundary : ∀ z ∈ (Icc a b ×ℂ Icc c d) \ (Ioo a b ×ℂ Ioo c d), f z ≠ 0) :
    ∃ S : Finset ℂ,
      (∀ z, z ∈ S ↔ z ∈ (Icc a b ×ℂ Icc c d) ∧ f z = 0) ∧
      (∀ z ∈ (Icc a b ×ℂ Icc c d), analyticOrderAt f z ≠ ⊤) ∧
      BoundaryIntegrable a b c d (logDeriv f) ∧
      boundary a b c d (logDeriv f) =
        (2 * (Real.pi : ℂ) * I) * ∑ rho ∈ S, (analyticOrderNatAt f rho : ℂ) := by
  classical
  obtain ⟨S, hmem, hinterior, horders⟩ :=
    RectangleZeros.exists_finset_rectangle_zeros a b c d hab hcd hf hboundary
  have hS : ∀ rho ∈ S, rho ∈ (Icc a b ×ℂ Icc c d) :=
    fun rho hrho => ((hmem rho).mp hrho).1
  have hfinite : ∀ rho ∈ S, analyticOrderAt f rho ≠ ⊤ :=
    fun rho hrho => horders rho (hS rho hrho)
  have hzeros : ∀ z ∈ (Icc a b ×ℂ Icc c d), f z = 0 → z ∈ S :=
    fun z hz hzero => (hmem z).mpr ⟨hz, hzero⟩
  obtain ⟨G, hG, hGEq⟩ :=
    PrincipalPart.exists_analyticOnNhd_logDeriv_sub_finite_principal_parts
      S hf hS hfinite hzeros
  have hGu : AnalyticOnNhd ℂ G (uIcc a b ×ℂ uIcc c d) := by
    simpa only [uIcc_of_le hab.le, uIcc_of_le hcd.le] using hG
  have hint : ∀ rho ∈ S,
      a < rho.re ∧ rho.re < b ∧ c < rho.im ∧ rho.im < d := by
    intro rho hrho
    rcases hinterior rho hrho with ⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩
    exact ⟨ha, hb, hc, hd⟩
  have hbottom (x : ℝ) : (x : ℂ) + (c : ℂ) * I ∉ S := by
    intro hz
    have hh := (hinterior _ hz).2.1
    have hc' : c < c := by simpa using hh
    exact (lt_irrefl c) hc'
  have htop (x : ℝ) : (x : ℂ) + (d : ℂ) * I ∉ S := by
    intro hz
    have hh := (hinterior _ hz).2.2
    have hd' : d < d := by simpa using hh
    exact (lt_irrefl d) hd'
  have hright (y : ℝ) : (b : ℂ) + (y : ℂ) * I ∉ S := by
    intro hz
    have hh := (hinterior _ hz).1.2
    have hb' : b < b := by simpa using hh
    exact (lt_irrefl b) hb'
  have hleft (y : ℝ) : (a : ℂ) + (y : ℂ) * I ∉ S := by
    intro hz
    have hh := (hinterior _ hz).1.1
    have ha' : a < a := by simpa using hh
    exact (lt_irrefl a) ha'
  let P : ℂ → ℂ := fun z =>
    ∑ rho ∈ S, (analyticOrderNatAt f rho : ℂ) / (z - rho)
  have hP : BoundaryIntegrable a b c d P :=
    finite_principal_parts_integrable a b c d S id
      (fun rho => (analyticOrderNatAt f rho : ℂ)) hint
  have hGI : BoundaryIntegrable a b c d G :=
    boundaryIntegrable_of_continuousOn a b c d G hGu.continuousOn
  have hplus (z : ℂ) (hz : z ∉ S) : G z + P z = logDeriv f z := by
    change G z + (∑ rho ∈ S, (analyticOrderNatAt f rho : ℂ) / (z - rho)) = _
    rw [hGEq z hz]
    exact sub_add_cancel _ _
  have hplusBoundary : BoundaryEq a b c d (fun z => G z + P z) (logDeriv f) :=
    ⟨fun x _ => hplus _ (hbottom x), fun x _ => hplus _ (htop x),
      fun y _ => hplus _ (hright y), fun y _ => hplus _ (hleft y)⟩
  have hlogI : BoundaryIntegrable a b c d (logDeriv f) :=
    boundaryIntegrable_congr a b c d (fun z => G z + P z) (logDeriv f)
      (hGI.add hP) hplusBoundary
  have hcorrectedBoundary : BoundaryEq a b c d G (fun z => logDeriv f z - P z) :=
    ⟨fun x _ => hGEq _ (hbottom x), fun x _ => hGEq _ (htop x),
      fun y _ => hGEq _ (hright y), fun y _ => hGEq _ (hleft y)⟩
  refine ⟨S, hmem, horders, hlogI, ?_⟩
  exact boundary_of_principal_part_extension a b c d (logDeriv f) G S id
    (fun rho => (analyticOrderNatAt f rho : ℂ)) hint hlogI hGu hcorrectedBoundary

end RiemannVonMangoldt.RectKernel

end
end P2MFinalSource007

/- Source module: PrincipalRegularizationV3
   Original SHA256: 887b7ca743e40b1c791014257e3c3dfe5b65c5117c5bf9bd691bdd9174edc399 -/
section P2MFinalSource008

open Complex Set Filter
open scoped Topology
set_option autoImplicit false

namespace RiemannVonMangoldt

/-- The genuine entire extension of `s*(s-1)*completedRiemannZeta s`.
The values at the two removed poles are supplied by the original entire
completed-zeta part; this is not naive multiplication of totalized pole values. -/
noncomputable def principalCompletedRegularization (s : ℂ) : ℂ :=
  1 + s * (s - 1) * completedRiemannZeta₀ s

theorem differentiable_principalCompletedRegularization :
    Differentiable ℂ principalCompletedRegularization := by
  change Differentiable ℂ
    (fun s : ℂ => 1 + s * (s - 1) * completedRiemannZeta₀ s)
  exact (differentiable_const (1 : ℂ)).add
    ((differentiable_id.mul (differentiable_id.sub_const (1 : ℂ))).mul
      differentiable_completedZeta₀)

theorem analyticOnNhd_principalCompletedRegularization :
    AnalyticOnNhd ℂ principalCompletedRegularization (univ : Set ℂ) :=
  differentiable_principalCompletedRegularization.differentiableOn.analyticOnNhd isOpen_univ

theorem analyticAt_principalCompletedRegularization (s : ℂ) :
    AnalyticAt ℂ principalCompletedRegularization s :=
  analyticOnNhd_principalCompletedRegularization s (mem_univ s)

@[simp] theorem principalCompletedRegularization_zero :
    principalCompletedRegularization 0 = 1 := by
  simp [principalCompletedRegularization]

@[simp] theorem principalCompletedRegularization_one :
    principalCompletedRegularization 1 = 1 := by
  simp [principalCompletedRegularization]

/-- Equality with the product at regular points follows from the exact original
completed-zeta identity, retaining both exceptional-point exclusions. -/
theorem principalCompletedRegularization_eq (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    principalCompletedRegularization s = s * (s - 1) * completedRiemannZeta s := by
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  rw [principalCompletedRegularization, completedRiemannZeta_eq]
  field_simp [hs0, h1s] <;> ring

theorem principalCompletedRegularization_eventuallyEq (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    principalCompletedRegularization =ᶠ[𝓝 s]
      (fun w : ℂ => w * (w - 1) * completedRiemannZeta w) := by
  filter_upwards [
    (continuousAt_id : ContinuousAt (fun w : ℂ => w) s).eventually_ne hs0,
    (continuousAt_id : ContinuousAt (fun w : ℂ => w) s).eventually_ne hs1]
    with w hw0 hw1
  exact principalCompletedRegularization_eq w hw0 hw1

theorem principalCompletedRegularization_ne_zero_iff (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    principalCompletedRegularization s ≠ 0 ↔ completedRiemannZeta s ≠ 0 := by
  rw [principalCompletedRegularization_eq s hs0 hs1]
  constructor
  · exact right_ne_zero_of_mul
  · intro h
    exact mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) h

/-- The two removed simple poles contribute `+1/s + 1/(s-1)` to the
regularized logarithmic derivative. Nonvanishing of the completed function
is explicit; no statement about contour counting is assumed. -/
theorem principalCompletedRegularization_logDeriv (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hC : completedRiemannZeta s ≠ 0) :
    logDeriv principalCompletedRegularization s =
      logDeriv completedRiemannZeta s + 1/s + 1/(s-1) := by
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hP : s * (s - 1) ≠ 0 := mul_ne_zero hs0 hs1'
  have hdP : DifferentiableAt ℂ (fun w : ℂ => w * (w - 1)) s :=
    differentiableAt_id.mul (differentiableAt_id.sub_const (1 : ℂ))
  have hdC : DifferentiableAt ℂ completedRiemannZeta s :=
    differentiableAt_completedZeta hs0 hs1
  have hpoly : logDeriv (fun w : ℂ => w * (w - 1)) s = 1/s + 1/(s-1) := by
    rw [logDeriv_mul (f := fun w : ℂ => w) (g := fun w : ℂ => w - 1)
      s hs0 hs1' differentiableAt_id (differentiableAt_id.sub_const (1 : ℂ))]
    simp [logDeriv_apply]
  rw [(logDeriv_congr_nhds
      (principalCompletedRegularization_eventuallyEq s hs0 hs1)).eq_of_nhds,
    logDeriv_mul (f := fun w : ℂ => w * (w - 1)) (g := completedRiemannZeta)
      s hP hC hdP hdC,
    hpoly]
  ring


end RiemannVonMangoldt
end P2MFinalSource008

/- Source module: DirichletMultiplicityV2
   Original SHA256: 7bfe95c194734671477246770becaabb26571ada99204dfb66bd8a70204586ec -/
section P2MFinalSource009

open Complex Set Filter
open scoped Topology
set_option autoImplicit false

namespace RiemannVonMangoldt
namespace CountBridge

variable {q : ℕ} [NeZero q]

/-- The actual inverse gamma factor is entire for either parity. -/
theorem analyticAt_gammaFactor_inv (χ : DirichletCharacter ℂ q) (s : ℂ) :
    AnalyticAt ℂ (fun w => (χ.gammaFactor w)⁻¹) s := by
  have hd : Differentiable ℂ (fun w => (χ.gammaFactor w)⁻¹) := by
    rcases χ.even_or_odd with he | ho
    · simpa only [he.gammaFactor_def] using differentiable_Gammaℝ_inv
    · simpa only [ho.gammaFactor_def, Function.comp_def, id_eq] using
        differentiable_Gammaℝ_inv.comp (differentiable_id.add_const (1 : ℂ))
  exact hd.analyticAt s

theorem gammaFactor_ne_zero_of_re_pos (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) : χ.gammaFactor s ≠ 0 := by
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [ho.gammaFactor_def]
    apply Gammaℝ_ne_zero_of_re_pos
    simpa only [add_re, one_re] using (show 0 < s.re + 1 by linarith)

theorem analyticAt_completedLFunction_of_ne (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    AnalyticAt ℂ χ.completedLFunction s := by
  apply analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [eventually_ne_nhds hs0, eventually_ne_nhds hs1] with w hw0 hw1
  exact χ.differentiableAt_completedLFunction w (.inl hw0) (.inl hw1)

/-- On the right half-plane, completion preserves the actual zero set. -/
theorem completedLFunction_eq_zero_iff_of_re_pos (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) :
    χ.completedLFunction s = 0 ↔ χ.LFunction s = 0 := by
  have hs0 : s ≠ 0 := by intro h; simpa [h] using hs
  rw [χ.LFunction_eq_completed_div_gammaFactor s (.inl hs0)]
  simp only [div_eq_zero_iff, gammaFactor_ne_zero_of_re_pos χ hs, or_false]

/-- Multiplicity equality is proved at the extended-natural order level first,
from the genuine completed/original identity and a nonzero analytic factor. -/
theorem analyticOrderAt_completedLFunction_eq (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    analyticOrderAt χ.completedLFunction s = analyticOrderAt χ.LFunction s := by
  have h0 : s ≠ 0 := by intro h; simpa [h] using hs0
  have h1 : s ≠ 1 := by intro h; simpa [h] using hs1
  have hC := analyticAt_completedLFunction_of_ne χ h0 h1
  have hG := analyticAt_gammaFactor_inv χ s
  have hG0 : (χ.gammaFactor s)⁻¹ ≠ 0 :=
    inv_ne_zero (gammaFactor_ne_zero_of_re_pos χ hs0)
  have heq : χ.LFunction =ᶠ[𝓝 s]
      (χ.completedLFunction * fun w => (χ.gammaFactor w)⁻¹) := by
    filter_upwards [eventually_ne_nhds h0] with w hw
    simpa only [Pi.mul_apply, div_eq_mul_inv] using
      χ.LFunction_eq_completed_div_gammaFactor w (.inl hw)
  symm
  calc
    analyticOrderAt χ.LFunction s =
        analyticOrderAt (χ.completedLFunction * fun w => (χ.gammaFactor w)⁻¹) s :=
      analyticOrderAt_congr heq
    _ = analyticOrderAt χ.completedLFunction s +
        analyticOrderAt (fun w => (χ.gammaFactor w)⁻¹) s := analyticOrderAt_mul hC hG
    _ = analyticOrderAt χ.completedLFunction s := by
      rw [hG.analyticOrderAt_eq_zero.mpr hG0, add_zero]

theorem analyticOrderNatAt_completedLFunction_eq (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    analyticOrderNatAt χ.completedLFunction s = analyticOrderNatAt χ.LFunction s := by
  simp only [analyticOrderNatAt, analyticOrderAt_completedLFunction_eq χ hs0 hs1]

theorem completedLFunction_ne_zero_of_one_le_re (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hχs : χ ≠ 1 ∨ s ≠ 1) (hs : 1 ≤ s.re) :
    χ.completedLFunction s ≠ 0 := by
  have hs0 : s ≠ 0 := by intro h; simp only [h, zero_re] at hs; linarith
  have hL := χ.LFunction_ne_zero_of_one_le_re hχs hs
  rw [χ.LFunction_eq_completed_div_gammaFactor s (.inl hs0)] at hL
  exact (div_ne_zero_iff.mp hL).1

/-- Reflection gives nonvanishing on the closed left half-plane, retaining the
actual principal exceptional point at zero. -/
theorem primitive_completedLFunction_ne_zero_of_re_le_zero
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive)
    {s : ℂ} (hχs : χ ≠ 1 ∨ s ≠ 0) (hs : s.re ≤ 0) :
    χ.completedLFunction s ≠ 0 := by
  have hpi : (χ⁻¹).IsPrimitive := by
    change (χ⁻¹).conductor = q
    rw [DirichletCharacter.conductor_inv]
    exact hp
  have hi : χ⁻¹ ≠ 1 ∨ 1 - s ≠ 1 := by
    rcases hχs with hχ | hs0
    · left
      intro h
      apply hχ
      have h' := congrArg (fun ξ : DirichletCharacter ℂ q => ξ⁻¹) h
      simpa only [inv_inv, inv_one] using h'
    · right
      intro h
      apply hs0
      linear_combination -h
  have hr : 1 ≤ (1 - s).re := by simp only [sub_re, one_re]; linarith
  have hC := completedLFunction_ne_zero_of_one_le_re (χ⁻¹) hi hr
  have heq : (χ⁻¹).completedLFunction (1 - s) =
      (q : ℂ) ^ (s - 1 / 2) * (χ⁻¹).rootNumber * χ.completedLFunction s := by
    simpa only [inv_inv] using hpi.completedLFunction_one_sub s
  rw [heq] at hC
  exact right_ne_zero_of_mul hC

theorem primitive_completedLFunction_zero_mem_criticalStrip
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    {s : ℂ} (hs : χ.completedLFunction s = 0) : 0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra h
    exact primitive_completedLFunction_ne_zero_of_re_le_zero χ hp (.inl hχ)
      (le_of_not_gt h) hs
  · by_contra h
    exact completedLFunction_ne_zero_of_one_le_re χ (.inl hχ) (le_of_not_gt h) hs

theorem principalCompletedRegularization_eq_zero_iff
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    principalCompletedRegularization s = 0 ↔ riemannZeta s = 0 := by
  have h0 : s ≠ 0 := by intro h; simpa [h] using hs0
  have h1 : s ≠ 1 := by intro h; simpa [h] using hs1
  have hP : s * (s - 1) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.mpr h1)
  rw [principalCompletedRegularization_eq s h0 h1, mul_eq_zero]
  simp only [hP, false_or]
  simpa only [DirichletCharacter.completedLFunction_modOne_eq,
    DirichletCharacter.LFunction_modOne_eq] using
    completedLFunction_eq_zero_iff_of_re_pos (1 : DirichletCharacter ℂ 1) hs0

theorem analyticOrderAt_principalCompletedRegularization_eq
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    analyticOrderAt principalCompletedRegularization s = analyticOrderAt riemannZeta s := by
  have h0 : s ≠ 0 := by intro h; simpa [h] using hs0
  have h1 : s ≠ 1 := by intro h; simpa [h] using hs1
  have hP : AnalyticAt ℂ (fun w : ℂ => w * (w - 1)) s := by fun_prop
  have hP0 : s * (s - 1) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.mpr h1)
  have hC : AnalyticAt ℂ completedRiemannZeta s := by
    simpa only [DirichletCharacter.completedLFunction_modOne_eq] using
      analyticAt_completedLFunction_of_ne (1 : DirichletCharacter ℂ 1) h0 h1
  calc
    analyticOrderAt principalCompletedRegularization s =
        analyticOrderAt ((fun w : ℂ => w * (w - 1)) * completedRiemannZeta) s :=
      analyticOrderAt_congr (principalCompletedRegularization_eventuallyEq s h0 h1)
    _ = analyticOrderAt (fun w : ℂ => w * (w - 1)) s +
        analyticOrderAt completedRiemannZeta s := analyticOrderAt_mul hP hC
    _ = analyticOrderAt completedRiemannZeta s := by
      rw [hP.analyticOrderAt_eq_zero.mpr hP0, zero_add]
    _ = analyticOrderAt riemannZeta s := by
      simpa only [DirichletCharacter.completedLFunction_modOne_eq,
        DirichletCharacter.LFunction_modOne_eq] using
        analyticOrderAt_completedLFunction_eq (1 : DirichletCharacter ℂ 1) hs0 hs1

theorem analyticOrderNatAt_principalCompletedRegularization_eq
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    analyticOrderNatAt principalCompletedRegularization s =
      analyticOrderNatAt riemannZeta s := by
  simp only [analyticOrderNatAt, analyticOrderAt_principalCompletedRegularization_eq hs0 hs1]

theorem principalCompletedRegularization_zero_mem_criticalStrip
    {s : ℂ} (hs : principalCompletedRegularization s = 0) : 0 < s.re ∧ s.re < 1 := by
  have h0 : s ≠ 0 := by intro h; simpa [h] using hs
  have h1 : s ≠ 1 := by intro h; simpa [h] using hs
  have hC : completedRiemannZeta s = 0 := by
    by_contra h
    exact ((principalCompletedRegularization_ne_zero_iff s h0 h1).mpr h) hs
  have hC' : (1 : DirichletCharacter ℂ 1).completedLFunction s = 0 := by
    simpa only [DirichletCharacter.completedLFunction_modOne_eq] using hC
  have hp : (1 : DirichletCharacter ℂ 1).IsPrimitive := by
    change (1 : DirichletCharacter ℂ 1).conductor = 1
    exact DirichletCharacter.conductor_one
  constructor
  · by_contra h
    exact primitive_completedLFunction_ne_zero_of_re_le_zero
      (1 : DirichletCharacter ℂ 1) hp (.inr h0) (le_of_not_gt h) hC'
  · by_contra h
    exact completedLFunction_ne_zero_of_one_le_re
      (1 : DirichletCharacter ℂ 1) (.inr h1) (le_of_not_gt h) hC'


end CountBridge
end RiemannVonMangoldt
end P2MFinalSource009

/- Source module: DirichletRectangleZerosV2
   Original SHA256: 9968c87164380a036399cf5b837fbc7e13049bb5010bd1eb3ae157180672ba10 -/
section P2MFinalSource010

open Complex Set Filter
open scoped Topology
set_option autoImplicit false

namespace RiemannVonMangoldt.CountBridge

/-- The original count's closed height condition places every critical-strip
point inside the actual contour rectangle, including points with zero height. -/
lemma criticalStrip_height_mem_rectangle {s : ℂ} {T : ℝ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hsT : |s.im| ≤ T) :
    s ∈ (Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-T) T) := by
  change ((-1 / 2 : ℝ) ≤ s.re ∧ s.re ≤ 3 / 2) ∧ -T ≤ s.im ∧ s.im ≤ T
  exact ⟨⟨by linarith, by linarith⟩, abs_le.mp hsT⟩

theorem primitive_principal_level_eq_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hχ : χ = 1) : q = 1 := by
  have hc : χ.conductor = q := hp
  rw [hχ, DirichletCharacter.conductor_one] at hc
  exact hc.symm

/-- Concrete nonprincipal carrier for the argument-principle sum and the
unchanged `dirichletZeroCount` predicate. Analytic orders are proved finite
before the natural-number weights are identified. -/
theorem exists_finset_completedLFunction_zeros
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hχ : χ ≠ 1) (T : ℝ) (hT : 0 < T)
    (hboundary : ∀ s ∈
      (Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-T) T) \
      (Ioo (-1 / 2 : ℝ) (3 / 2) ×ℂ Ioo (-T) T), χ.completedLFunction s ≠ 0) :
    ∃ S : Finset ℂ,
      (∀ s, s ∈ S ↔
        s ∈ (Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-T) T) ∧
          χ.completedLFunction s = 0) ∧
      (∀ s, s ∈ S ↔
        0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧ χ.LFunction s = 0) ∧
      (∀ s ∈ S, s ∈ (Ioo (-1 / 2 : ℝ) (3 / 2) ×ℂ Ioo (-T) T)) ∧
      (∀ s ∈ (Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-T) T),
        analyticOrderAt χ.completedLFunction s ≠ ⊤) ∧
      (∀ s ∈ S, analyticOrderAt χ.LFunction s ≠ ⊤) ∧
      (∀ s ∈ S,
        analyticOrderNatAt χ.completedLFunction s = analyticOrderNatAt χ.LFunction s) := by
  have hf : AnalyticOnNhd ℂ χ.completedLFunction
      (Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-T) T) := by
    intro s _
    exact (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt s
  obtain ⟨S, hS, hinterior, horders⟩ := RectangleZeros.exists_finset_rectangle_zeros
    (-1 / 2) (3 / 2) (-T) T (by norm_num) (by linarith) hf hboundary
  have hcarrier (s : ℂ) : s ∈ S ↔
      0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧ χ.LFunction s = 0 := by
    constructor
    · intro hs
      obtain ⟨hsR, hsC⟩ := (hS s).mp hs
      obtain ⟨hs0, hs1⟩ := primitive_completedLFunction_zero_mem_criticalStrip χ hp hχ hsC
      refine ⟨hs0, hs1, abs_le.mpr hsR.2, ?_⟩
      exact (completedLFunction_eq_zero_iff_of_re_pos χ hs0).mp hsC
    · rintro ⟨hs0, hs1, hsT, hsL⟩
      exact (hS s).mpr ⟨criticalStrip_height_mem_rectangle hs0 hs1 hsT,
        (completedLFunction_eq_zero_iff_of_re_pos χ hs0).mpr hsL⟩
  refine ⟨S, hS, hcarrier, hinterior, horders, ?_, ?_⟩
  · intro s hs
    obtain ⟨hs0, hs1, _, _⟩ := (hcarrier s).mp hs
    rw [← analyticOrderAt_completedLFunction_eq χ hs0 hs1]
    exact horders s ((hS s).mp hs).1
  · intro s hs
    obtain ⟨hs0, hs1, _, _⟩ := (hcarrier s).mp hs
    exact analyticOrderNatAt_completedLFunction_eq χ hs0 hs1

/-- The principal carrier uses the genuine entire regularization. Its values
at zero and one are nonzero, so neither pole is counted as a zero. The
character is the original (unique) character of level one. -/
theorem exists_finset_principalCompletedRegularization_zeros
    (χ : DirichletCharacter ℂ 1) (T : ℝ) (hT : 0 < T)
    (hboundary : ∀ s ∈
      (Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-T) T) \
      (Ioo (-1 / 2 : ℝ) (3 / 2) ×ℂ Ioo (-T) T),
        principalCompletedRegularization s ≠ 0) :
    ∃ S : Finset ℂ,
      (∀ s, s ∈ S ↔
        s ∈ (Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-T) T) ∧
          principalCompletedRegularization s = 0) ∧
      (∀ s, s ∈ S ↔
        0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧ χ.LFunction s = 0) ∧
      (∀ s ∈ S, s ∈ (Ioo (-1 / 2 : ℝ) (3 / 2) ×ℂ Ioo (-T) T)) ∧
      (∀ s ∈ (Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-T) T),
        analyticOrderAt principalCompletedRegularization s ≠ ⊤) ∧
      (∀ s ∈ S, analyticOrderAt χ.LFunction s ≠ ⊤) ∧
      (∀ s ∈ S,
        analyticOrderNatAt principalCompletedRegularization s =
          analyticOrderNatAt χ.LFunction s) := by
  have hf : AnalyticOnNhd ℂ principalCompletedRegularization
      (Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-T) T) := by
    intro s _
    exact analyticAt_principalCompletedRegularization s
  obtain ⟨S, hS, hinterior, horders⟩ := RectangleZeros.exists_finset_rectangle_zeros
    (-1 / 2) (3 / 2) (-T) T (by norm_num) (by linarith) hf hboundary
  have hcarrier (s : ℂ) : s ∈ S ↔
      0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧ χ.LFunction s = 0 := by
    constructor
    · intro hs
      obtain ⟨hsR, hsF⟩ := (hS s).mp hs
      obtain ⟨hs0, hs1⟩ := principalCompletedRegularization_zero_mem_criticalStrip hsF
      refine ⟨hs0, hs1, abs_le.mpr hsR.2, ?_⟩
      simpa only [DirichletCharacter.LFunction_modOne_eq] using
        (principalCompletedRegularization_eq_zero_iff hs0 hs1).mp hsF
    · rintro ⟨hs0, hs1, hsT, hsL⟩
      refine (hS s).mpr ⟨criticalStrip_height_mem_rectangle hs0 hs1 hsT, ?_⟩
      apply (principalCompletedRegularization_eq_zero_iff hs0 hs1).mpr
      simpa only [DirichletCharacter.LFunction_modOne_eq] using hsL
  refine ⟨S, hS, hcarrier, hinterior, horders, ?_, ?_⟩
  · intro s hs
    obtain ⟨hs0, hs1, _, _⟩ := (hcarrier s).mp hs
    simp only [DirichletCharacter.LFunction_modOne_eq]
    rw [← analyticOrderAt_principalCompletedRegularization_eq hs0 hs1]
    exact horders s ((hS s).mp hs).1
  · intro s hs
    obtain ⟨hs0, hs1, _, _⟩ := (hcarrier s).mp hs
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      analyticOrderNatAt_principalCompletedRegularization_eq hs0 hs1


end RiemannVonMangoldt.CountBridge
end P2MFinalSource010

/- Source module: DirichletCountFinsumV1
   Original SHA256: af445a1d2612a929d9ec478a7ea7614d25edf6e3e1a6ce5792ea39118041128a -/
section P2MFinalSource011

/-!
Convert an exact finite carrier to the unchanged public dirichletZeroCount.
The carrier equivalence retains the open real critical strip, both signed
heights, closed height endpoints and every real zero. Multiplicities remain
the original L-function's actual analyticOrderNatAt.

The optional order-transport interface permits the completed or regularized
analytic function's finite sum to be identified with that same public count.
-/

set_option autoImplicit false

open Complex Set
open scoped BigOperators

namespace RiemannVonMangoldt.CountBridge

theorem dirichletZeroCount_eq_finset_sum
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (T : ℝ) (S : Finset ℂ)
    (hS : ∀ z : ℂ, z ∈ S ↔
      0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T ∧ chi.LFunction z = 0) :
    dirichletZeroCount chi T =
      ∑ z ∈ S, (analyticOrderNatAt chi.LFunction z : ℝ) := by
  have hset :
      {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T ∧ chi.LFunction z = 0} =
        (S : Set ℂ) := by
    apply Set.ext
    intro z
    exact (hS z).symm
  unfold dirichletZeroCount
  rw [hset, finsum_mem_coe_finset]

theorem ofReal_dirichletZeroCount_eq_finset_sum
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (T : ℝ) (S : Finset ℂ)
    (hS : ∀ z : ℂ, z ∈ S ↔
      0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T ∧ chi.LFunction z = 0) :
    (dirichletZeroCount chi T : ℂ) =
      ∑ z ∈ S, (analyticOrderNatAt chi.LFunction z : ℂ) := by
  rw [dirichletZeroCount_eq_finset_sum chi T S hS]
  norm_cast

theorem dirichletZeroCount_eq_finset_sum_of_orders
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (T : ℝ)
    (S : Finset ℂ) (f : ℂ → ℂ)
    (hS : ∀ z : ℂ, z ∈ S ↔
      0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T ∧ chi.LFunction z = 0)
    (horder : ∀ z ∈ S, analyticOrderNatAt f z = analyticOrderNatAt chi.LFunction z) :
    dirichletZeroCount chi T = ∑ z ∈ S, (analyticOrderNatAt f z : ℝ) := by
  rw [dirichletZeroCount_eq_finset_sum chi T S hS]
  apply Finset.sum_congr rfl
  intro z hz
  rw [horder z hz]

theorem ofReal_dirichletZeroCount_eq_finset_sum_of_orders
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (T : ℝ)
    (S : Finset ℂ) (f : ℂ → ℂ)
    (hS : ∀ z : ℂ, z ∈ S ↔
      0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T ∧ chi.LFunction z = 0)
    (horder : ∀ z ∈ S, analyticOrderNatAt f z = analyticOrderNatAt chi.LFunction z) :
    (dirichletZeroCount chi T : ℂ) = ∑ z ∈ S, (analyticOrderNatAt f z : ℂ) := by
  rw [dirichletZeroCount_eq_finset_sum_of_orders chi T S f hS horder]
  norm_cast

end RiemannVonMangoldt.CountBridge

end P2MFinalSource011

/- Source module: DirichletBoundaryCountV1
   Original SHA256: 87d925730ea4574be7115d94e1e9b997798451d431a9260ac6680edde0710387 -/
section P2MFinalSource012

/-!
Identify the actual analytic contour multiplicity sum with the unchanged
public Dirichlet zero count. The two finite carriers are proved equal from
their exact zero predicates. No finite-zero or finite-order premise is added.
The principal theorem here uses the genuine entire regularization; its two
pole corrections are discharged in the following composition.
-/

set_option autoImplicit false

open Complex Set
open scoped BigOperators

namespace RiemannVonMangoldt.CountBridge

open RectKernel

theorem completedLFunction_boundary_count_nonprincipal
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hp : chi.IsPrimitive) (hchi : chi ≠ 1) (T : ℝ) (hT : 0 < T)
    (hboundary : ∀ z ∈
      (Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-T) T) \
      (Ioo (-1 / 2 : ℝ) (3 / 2) ×ℂ Ioo (-T) T),
        chi.completedLFunction z ≠ 0) :
    BoundaryIntegrable (-1 / 2) (3 / 2) (-T) T (logDeriv chi.completedLFunction) ∧
      boundary (-1 / 2) (3 / 2) (-T) T (logDeriv chi.completedLFunction) =
        (2 * (Real.pi : ℂ) * I) * (dirichletZeroCount chi T : ℂ) := by
  classical
  have hf : AnalyticOnNhd ℂ chi.completedLFunction
      (Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-T) T) := by
    intro z _
    exact (DirichletCharacter.differentiable_completedLFunction hchi).analyticAt z
  obtain ⟨S, hS, _, hInt, hB⟩ := analytic_rectangle_logDeriv_count
    (-1 / 2) (3 / 2) (-T) T (by norm_num) (by linarith) hf hboundary
  obtain ⟨Z, hZ, hZcount, _, _, _, hZweights⟩ :=
    exists_finset_completedLFunction_zeros chi hp hchi T hT hboundary
  have hSZ : S = Z := by
    apply Finset.ext
    intro z
    exact (hS z).trans (hZ z).symm
  have hcount := ofReal_dirichletZeroCount_eq_finset_sum_of_orders
    chi T Z chi.completedLFunction hZcount hZweights
  rw [hSZ, ← hcount] at hB
  exact ⟨hInt, hB⟩

theorem principalCompletedRegularization_boundary_count
    (chi : DirichletCharacter ℂ 1) (T : ℝ) (hT : 0 < T)
    (hboundary : ∀ z ∈
      (Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-T) T) \
      (Ioo (-1 / 2 : ℝ) (3 / 2) ×ℂ Ioo (-T) T),
        principalCompletedRegularization z ≠ 0) :
    BoundaryIntegrable (-1 / 2) (3 / 2) (-T) T
        (logDeriv principalCompletedRegularization) ∧
      boundary (-1 / 2) (3 / 2) (-T) T
          (logDeriv principalCompletedRegularization) =
        (2 * (Real.pi : ℂ) * I) * (dirichletZeroCount chi T : ℂ) := by
  classical
  have hf : AnalyticOnNhd ℂ principalCompletedRegularization
      (Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-T) T) := by
    intro z _
    exact analyticAt_principalCompletedRegularization z
  obtain ⟨S, hS, _, hInt, hB⟩ := analytic_rectangle_logDeriv_count
    (-1 / 2) (3 / 2) (-T) T (by norm_num) (by linarith) hf hboundary
  obtain ⟨Z, hZ, hZcount, _, _, _, hZweights⟩ :=
    exists_finset_principalCompletedRegularization_zeros chi T hT hboundary
  have hSZ : S = Z := by
    apply Finset.ext
    intro z
    exact (hS z).trans (hZ z).symm
  have hcount := ofReal_dirichletZeroCount_eq_finset_sum_of_orders
    chi T Z principalCompletedRegularization hZcount hZweights
  rw [hSZ, ← hcount] at hB
  exact ⟨hInt, hB⟩

end RiemannVonMangoldt.CountBridge

end P2MFinalSource012

/- Source module: DirichletGoodHeightBoundaryV2
   Original SHA256: 9ea876dc791f0628306c6893d1f0b3bd82873898899b3db5fd843e1362badabf -/
section P2MFinalSource013

open Complex Set Filter
open scoped Topology
set_option autoImplicit false

namespace RiemannVonMangoldt.CountBridge

/-- Good-height nonvanishing on the right half of the contour for `χ`,
together with the reflected height for `χ⁻¹`, gives the entire horizontal
side. The functional equation itself supplies the reflection. -/
theorem primitive_completedLFunction_ne_zero_horizontal_of_paired
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive)
    (t : ℝ)
    (hχ : ∀ σ ∈ Icc (1 / 2 : ℝ) (3 / 2),
      χ.LFunction ((σ : ℂ) + (t : ℂ) * I) ≠ 0)
    (hi : ∀ σ ∈ Icc (1 / 2 : ℝ) (3 / 2),
      (χ⁻¹).LFunction ((σ : ℂ) + ((-t : ℝ) : ℂ) * I) ≠ 0)
    (σ : ℝ) (hσ : σ ∈ Icc (-1 / 2 : ℝ) (3 / 2)) :
    χ.completedLFunction ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
  by_cases hhalf : (1 / 2 : ℝ) ≤ σ
  · have hspos : 0 < ((σ : ℂ) + (t : ℂ) * I).re := by
      simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
        mul_zero, zero_mul, sub_zero, add_zero]
      linarith
    intro hC
    exact hχ σ ⟨hhalf, hσ.2⟩
      ((completedLFunction_eq_zero_iff_of_re_pos χ hspos).mp hC)
  · have hσ' : 1 - σ ∈ Icc (1 / 2 : ℝ) (3 / 2) := by
      constructor <;> linarith [hσ.1]
    have hrep : 1 - ((σ : ℂ) + (t : ℂ) * I) =
        ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
      push_cast
      ring
    have hC : (χ⁻¹).completedLFunction (1 - ((σ : ℂ) + (t : ℂ) * I)) ≠ 0 := by
      rw [hrep]
      have hspos : 0 < (((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I).re := by
        simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
          mul_zero, zero_mul, sub_zero, add_zero]
        linarith [hσ'.1]
      intro hz
      exact hi (1 - σ) hσ'
        ((completedLFunction_eq_zero_iff_of_re_pos (χ⁻¹) hspos).mp hz)
    have hpi : (χ⁻¹).IsPrimitive := by
      change (χ⁻¹).conductor = q
      rw [DirichletCharacter.conductor_inv]
      exact hp
    have heq := hpi.completedLFunction_one_sub ((σ : ℂ) + (t : ℂ) * I)
    simp only [inv_inv] at heq
    rw [heq] at hC
    exact right_ne_zero_of_mul hC

lemma rectangle_boundary_coordinate {s : ℂ} {T : ℝ}
    (hs : s ∈ (Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-T) T) \
      (Ioo (-1 / 2 : ℝ) (3 / 2) ×ℂ Ioo (-T) T)) :
    s.re = -1 / 2 ∨ s.re = 3 / 2 ∨ s.im = -T ∨ s.im = T := by
  by_cases hl : s.re = -1 / 2
  · exact .inl hl
  by_cases hr : s.re = 3 / 2
  · exact .inr (.inl hr)
  by_cases hb : s.im = -T
  · exact .inr (.inr (.inl hb))
  by_cases ht : s.im = T
  · exact .inr (.inr (.inr ht))
  exact (hs.2 ⟨⟨lt_of_le_of_ne hs.1.1.1 (Ne.symm hl),
    lt_of_le_of_ne hs.1.1.2 hr⟩,
      ⟨lt_of_le_of_ne hs.1.2.1 (Ne.symm hb), lt_of_le_of_ne hs.1.2.2 ht⟩⟩).elim

/-- This boundary statement includes the principal character. At the vertical
edges, the genuine half-plane nonvanishing lemmas keep the pole exclusions;
the horizontal edges use the paired signed-height hypotheses verbatim. -/
theorem primitive_completedLFunction_boundary_of_paired_good_heights
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (T : ℝ)
    (hχpos : ∀ σ ∈ Icc (1 / 2 : ℝ) (3 / 2),
      χ.LFunction ((σ : ℂ) + (T : ℂ) * I) ≠ 0)
    (hχneg : ∀ σ ∈ Icc (1 / 2 : ℝ) (3 / 2),
      χ.LFunction ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0)
    (hipos : ∀ σ ∈ Icc (1 / 2 : ℝ) (3 / 2),
      (χ⁻¹).LFunction ((σ : ℂ) + (T : ℂ) * I) ≠ 0)
    (hineg : ∀ σ ∈ Icc (1 / 2 : ℝ) (3 / 2),
      (χ⁻¹).LFunction ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0) :
    ∀ s ∈ (Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-T) T) \
      (Ioo (-1 / 2 : ℝ) (3 / 2) ×ℂ Ioo (-T) T), χ.completedLFunction s ≠ 0 := by
  intro s hs
  rcases rectangle_boundary_coordinate hs with hl | hr | hb | ht
  · have hs0 : s ≠ 0 := by
      intro h
      have he := congrArg Complex.re h
      simp only [zero_re] at he
      linarith
    exact primitive_completedLFunction_ne_zero_of_re_le_zero χ hp (.inr hs0)
      (by rw [hl]; norm_num)
  · have hs1 : s ≠ 1 := by
      intro h
      have he := congrArg Complex.re h
      simp only [one_re] at he
      linarith
    exact completedLFunction_ne_zero_of_one_le_re χ (.inr hs1)
      (by rw [hr]; norm_num)
  · rw [← Complex.re_add_im s, hb]
    exact primitive_completedLFunction_ne_zero_horizontal_of_paired χ hp (-T)
      hχneg (by simpa only [neg_neg] using hipos) s.re hs.1.1
  · rw [← Complex.re_add_im s, ht]
    exact primitive_completedLFunction_ne_zero_horizontal_of_paired χ hp T
      hχpos hineg s.re hs.1.1

lemma rectangle_boundary_ne_zero_ne_one {s : ℂ} {T : ℝ} (hT : 0 < T)
    (hs : s ∈ (Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-T) T) \
      (Ioo (-1 / 2 : ℝ) (3 / 2) ×ℂ Ioo (-T) T)) : s ≠ 0 ∧ s ≠ 1 := by
  constructor
  · intro h
    apply hs.2
    rw [h]
    change ((-1 / 2 : ℝ) < 0 ∧ 0 < 3 / 2) ∧ -T < 0 ∧ 0 < T
    exact ⟨⟨by norm_num, by norm_num⟩, ⟨by linarith, hT⟩⟩
  · intro h
    apply hs.2
    rw [h]
    change ((-1 / 2 : ℝ) < 1 ∧ 1 < 3 / 2) ∧ -T < 0 ∧ 0 < T
    exact ⟨⟨by norm_num, by norm_num⟩, ⟨by linarith, hT⟩⟩

/-- The same four good-height hypotheses give nonvanishing of the actual
entire principal regularization, with both polynomial factors nonzero on
the contour. -/
theorem principalCompletedRegularization_boundary_of_paired_good_heights
    (χ : DirichletCharacter ℂ 1) (hp : χ.IsPrimitive) (T : ℝ) (hT : 0 < T)
    (hχpos : ∀ σ ∈ Icc (1 / 2 : ℝ) (3 / 2),
      χ.LFunction ((σ : ℂ) + (T : ℂ) * I) ≠ 0)
    (hχneg : ∀ σ ∈ Icc (1 / 2 : ℝ) (3 / 2),
      χ.LFunction ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0)
    (hipos : ∀ σ ∈ Icc (1 / 2 : ℝ) (3 / 2),
      (χ⁻¹).LFunction ((σ : ℂ) + (T : ℂ) * I) ≠ 0)
    (hineg : ∀ σ ∈ Icc (1 / 2 : ℝ) (3 / 2),
      (χ⁻¹).LFunction ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0) :
    ∀ s ∈ (Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-T) T) \
      (Ioo (-1 / 2 : ℝ) (3 / 2) ×ℂ Ioo (-T) T),
        principalCompletedRegularization s ≠ 0 := by
  intro s hs
  obtain ⟨hs0, hs1⟩ := rectangle_boundary_ne_zero_ne_one hT hs
  apply (principalCompletedRegularization_ne_zero_iff s hs0 hs1).mpr
  simpa only [DirichletCharacter.completedLFunction_modOne_eq] using
    primitive_completedLFunction_boundary_of_paired_good_heights χ hp T
      hχpos hχneg hipos hineg s hs


end RiemannVonMangoldt.CountBridge
end P2MFinalSource013

/- Source module: DirichletArgumentPrincipleV2
   Original SHA256: 32c94e0d36a068bd4bd8685bb8d45693a3c38a745e049257ea674218ded835f4 -/
section P2MFinalSource014

/-!
The exact completed Dirichlet contour formula, including the principal
character's two pole corrections. These corrections are the actual
reciprocal integrals at zero and one. All four edge integrabilities are
derived, and the count is the unchanged original definition.
-/

set_option autoImplicit false

open Complex Set Classical
open scoped Interval BigOperators

namespace RiemannVonMangoldt.CountBridge

open RectKernel

private lemma countRectangle_boundaryEq {T : ℝ} (hT : 0 < T)
    {f g : ℂ → ℂ}
    (hEq : EqOn f g
      ((Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-T) T) \
        (Ioo (-1 / 2 : ℝ) (3 / 2) ×ℂ Ioo (-T) T))) :
    BoundaryEq (-1 / 2) (3 / 2) (-T) T f g := by
  have hab : (-1 / 2 : ℝ) ≤ 3 / 2 := by norm_num
  have hcd : -T ≤ T := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ Icc (-1 / 2 : ℝ) (3 / 2) := by
      simpa only [uIcc_of_le hab] using hx
    apply hEq
    refine ⟨?_, ?_⟩
    · change
        (((x : ℂ) + ((-T : ℝ) : ℂ) * I).re ∈ Icc (-1 / 2 : ℝ) (3 / 2)) ∧
        (((x : ℂ) + ((-T : ℝ) : ℂ) * I).im ∈ Icc (-T) T)
      simpa using And.intro hx' (show -T ∈ Icc (-T) T from ⟨le_rfl, hcd⟩)
    · intro hz
      have hh : -T < -T := by simpa using hz.2.1
      exact (lt_irrefl (-T)) hh
  · intro x hx
    have hx' : x ∈ Icc (-1 / 2 : ℝ) (3 / 2) := by
      simpa only [uIcc_of_le hab] using hx
    apply hEq
    refine ⟨?_, ?_⟩
    · change
        (((x : ℂ) + (T : ℂ) * I).re ∈ Icc (-1 / 2 : ℝ) (3 / 2)) ∧
        (((x : ℂ) + (T : ℂ) * I).im ∈ Icc (-T) T)
      simpa using And.intro hx' (show T ∈ Icc (-T) T from ⟨hcd, le_rfl⟩)
    · intro hz
      have hh : T < T := by simpa using hz.2.2
      exact (lt_irrefl T) hh
  · intro y hy
    have hy' : y ∈ Icc (-T) T := by
      simpa only [uIcc_of_le hcd] using hy
    apply hEq
    refine ⟨?_, ?_⟩
    · change
        ((((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I).re ∈ Icc (-1 / 2 : ℝ) (3 / 2)) ∧
        ((((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I).im ∈ Icc (-T) T)
      simpa using And.intro (show (3 / 2 : ℝ) ∈ Icc (-1 / 2 : ℝ) (3 / 2)
        from ⟨hab, le_rfl⟩) hy'
    · intro hz
      have hh : (3 / 2 : ℝ) < 3 / 2 := by simpa using hz.1.2
      exact (lt_irrefl (3 / 2 : ℝ)) hh
  · intro y hy
    have hy' : y ∈ Icc (-T) T := by
      simpa only [uIcc_of_le hcd] using hy
    apply hEq
    refine ⟨?_, ?_⟩
    · change
        ((((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I).re ∈ Icc (-1 / 2 : ℝ) (3 / 2)) ∧
        ((((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I).im ∈ Icc (-T) T)
      simpa using And.intro (show (-1 / 2 : ℝ) ∈ Icc (-1 / 2 : ℝ) (3 / 2)
        from ⟨le_rfl, hab⟩) hy'
    · intro hz
      have hh : (-1 / 2 : ℝ) < -1 / 2 := by simpa using hz.1.1
      exact (lt_irrefl (-1 / 2 : ℝ)) hh

/-- The level-one completed function has the two original simple poles.
The entire regularization counts exactly the original L-function zeros;
subtracting the two checked reciprocal boundary integrals gives the pole
correction with its actual sign and multiplicity. -/
theorem completedLFunction_boundary_count_principal
    (chi : DirichletCharacter ℂ 1) (T : ℝ) (hT : 0 < T)
    (hboundary : ∀ z ∈
      (Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-T) T) \
      (Ioo (-1 / 2 : ℝ) (3 / 2) ×ℂ Ioo (-T) T),
        chi.completedLFunction z ≠ 0) :
    BoundaryIntegrable (-1 / 2) (3 / 2) (-T) T (logDeriv chi.completedLFunction) ∧
      boundary (-1 / 2) (3 / 2) (-T) T (logDeriv chi.completedLFunction) =
        (2 * (Real.pi : ℂ) * I) * ((dirichletZeroCount chi T : ℂ) - 2) := by
  have hC : ∀ z ∈
      (Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-T) T) \
      (Ioo (-1 / 2 : ℝ) (3 / 2) ×ℂ Ioo (-T) T),
        completedRiemannZeta z ≠ 0 := by
    intro z hz
    simpa only [DirichletCharacter.completedLFunction_modOne_eq] using hboundary z hz
  have hF : ∀ z ∈
      (Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-T) T) \
      (Ioo (-1 / 2 : ℝ) (3 / 2) ×ℂ Ioo (-T) T),
        principalCompletedRegularization z ≠ 0 := by
    intro z hz
    obtain ⟨hz0, hz1⟩ := rectangle_boundary_ne_zero_ne_one hT hz
    exact (principalCompletedRegularization_ne_zero_iff z hz0 hz1).mpr (hC z hz)
  obtain ⟨hFI, hFB⟩ := principalCompletedRegularization_boundary_count chi T hT hF
  have h0c : -T < (0 : ℂ).im := by change -T < 0; linarith
  have h0d : (0 : ℂ).im < T := by change 0 < T; exact hT
  have h1c : -T < (1 : ℂ).im := by change -T < 0; linarith
  have h1d : (1 : ℂ).im < T := by change 0 < T; exact hT
  have h0I := boundaryIntegrable_reciprocal (-1 / 2) (3 / 2) (-T) T (0 : ℂ)
    (by norm_num) (by norm_num) h0c h0d
  have h1I := boundaryIntegrable_reciprocal (-1 / 2) (3 / 2) (-T) T (1 : ℂ)
    (by norm_num) (by norm_num) h1c h1d
  have h0B := boundary_reciprocal (-1 / 2) (3 / 2) (-T) T (0 : ℂ)
    (by norm_num) (by norm_num) h0c h0d
  have h1B := boundary_reciprocal (-1 / 2) (3 / 2) (-T) T (1 : ℂ)
    (by norm_num) (by norm_num) h1c h1d
  let D : ℂ → ℂ := fun z =>
    logDeriv principalCompletedRegularization z - 1 / (z - 0) - 1 / (z - 1)
  have hDI : BoundaryIntegrable (-1 / 2) (3 / 2) (-T) T D :=
    (hFI.sub h0I).sub h1I
  have hEq : BoundaryEq (-1 / 2) (3 / 2) (-T) T D (logDeriv completedRiemannZeta) := by
    apply countRectangle_boundaryEq hT
    intro z hz
    obtain ⟨hz0, hz1⟩ := rectangle_boundary_ne_zero_ne_one hT hz
    change logDeriv principalCompletedRegularization z - 1 / (z - 0) -
      1 / (z - 1) = logDeriv completedRiemannZeta z
    rw [principalCompletedRegularization_logDeriv z hz0 hz1 (hC z hz)]
    simp only [sub_zero]
    ring
  have hCI : BoundaryIntegrable (-1 / 2) (3 / 2) (-T) T
      (logDeriv completedRiemannZeta) :=
    boundaryIntegrable_congr (-1 / 2) (3 / 2) (-T) T D
      (logDeriv completedRiemannZeta) hDI hEq
  have hCB : boundary (-1 / 2) (3 / 2) (-T) T (logDeriv completedRiemannZeta) =
      (2 * (Real.pi : ℂ) * I) * ((dirichletZeroCount chi T : ℂ) - 2) := by
    rw [← boundary_congr (-1 / 2) (3 / 2) (-T) T D
      (logDeriv completedRiemannZeta) hEq]
    change boundary (-1 / 2) (3 / 2) (-T) T
        (fun z => logDeriv principalCompletedRegularization z -
          1 / (z - 0) - 1 / (z - 1)) = _
    rw [boundary_sub (-1 / 2) (3 / 2) (-T) T _ _ (hFI.sub h0I) h1I,
      boundary_sub (-1 / 2) (3 / 2) (-T) T _ _ hFI h0I, hFB, h0B, h1B]
    ring
  simpa only [DirichletCharacter.completedLFunction_modOne_eq] using And.intro hCI hCB

/-- Exact contour counting for every primitive character. The principal
correction is derived from its two poles, after reduction to level one. -/
theorem primitive_completedLFunction_boundary_count
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hp : chi.IsPrimitive) (T : ℝ) (hT : 0 < T)
    (hboundary : ∀ z ∈
      (Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-T) T) \
      (Ioo (-1 / 2 : ℝ) (3 / 2) ×ℂ Ioo (-T) T),
        chi.completedLFunction z ≠ 0) :
    BoundaryIntegrable (-1 / 2) (3 / 2) (-T) T (logDeriv chi.completedLFunction) ∧
      boundary (-1 / 2) (3 / 2) (-T) T (logDeriv chi.completedLFunction) =
        (2 * (Real.pi : ℂ) * I) *
          ((dirichletZeroCount chi T : ℂ) - (if chi = 1 then (2 : ℂ) else 0)) := by
  classical
  by_cases hchi : chi = 1
  · have hq := primitive_principal_level_eq_one chi hp hchi
    subst q
    simpa only [if_pos hchi] using
      completedLFunction_boundary_count_principal chi T hT hboundary
  · simpa only [if_neg hchi, sub_zero] using
      completedLFunction_boundary_count_nonprincipal chi hp hchi T hT hboundary

/-- The exact original-count identity at the paired signed good heights used
by the contour estimates. Boundary nonvanishing is a conclusion of the
genuine functional equation and the four given L-function conditions. -/
theorem primitive_completedLFunction_boundary_count_of_paired_good_heights
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hp : chi.IsPrimitive) (T : ℝ) (hT : 0 < T)
    (hchipos : ∀ σ ∈ Icc (1 / 2 : ℝ) (3 / 2),
      chi.LFunction ((σ : ℂ) + (T : ℂ) * I) ≠ 0)
    (hchineg : ∀ σ ∈ Icc (1 / 2 : ℝ) (3 / 2),
      chi.LFunction ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0)
    (hipos : ∀ σ ∈ Icc (1 / 2 : ℝ) (3 / 2),
      (chi⁻¹).LFunction ((σ : ℂ) + (T : ℂ) * I) ≠ 0)
    (hineg : ∀ σ ∈ Icc (1 / 2 : ℝ) (3 / 2),
      (chi⁻¹).LFunction ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0) :
    BoundaryIntegrable (-1 / 2) (3 / 2) (-T) T (logDeriv chi.completedLFunction) ∧
      boundary (-1 / 2) (3 / 2) (-T) T (logDeriv chi.completedLFunction) =
        (2 * (Real.pi : ℂ) * I) *
          ((dirichletZeroCount chi T : ℂ) - (if chi = 1 then (2 : ℂ) else 0)) :=
  primitive_completedLFunction_boundary_count chi hp T hT
    (primitive_completedLFunction_boundary_of_paired_good_heights chi hp T
      hchipos hchineg hipos hineg)

end RiemannVonMangoldt.CountBridge

end P2MFinalSource014

/- Source module: AcceptedReflectionPrefixV1
   Original SHA256: 9f1d17fcfc909eaa346a2c69f121927f06861b913746dbdd31453e2cf2a69995 -/
section P2MFinalSource015

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology

namespace Helfgott

noncomputable def gammaApproxKernel (n : ℕ) : ℝ → ℂ :=
  (Ioc (0 : ℝ) (n : ℝ)).indicator (fun t : ℝ => (((1-t/n)^n : ℝ) : ℂ))

lemma gammaApproxKernel_norm_bound (n : ℕ) (t : ℝ) (ht : 0 < t) :
    ‖gammaApproxKernel n t‖ ≤ Real.exp (-t) := by
  by_cases htn : t ≤ (n : ℝ)
  · rw [gammaApproxKernel,indicator_of_mem (show t ∈ Ioc (0 : ℝ) n from ⟨ht,htn⟩),
      Complex.norm_of_nonneg (pow_nonneg (sub_nonneg.mpr
        (div_le_one_of_le₀ htn (by positivity))) _)]
    exact Real.one_sub_div_pow_le_exp_neg htn
  · rw [gammaApproxKernel,indicator_of_notMem (notMem_Ioc_of_gt (lt_of_not_ge htn)),norm_zero]
    exact Real.exp_nonneg _

lemma gammaApproxKernel_locallyIntegrable (n : ℕ) : LocallyIntegrable (gammaApproxKernel n) :=
  ((show Continuous (fun t : ℝ => (((1-t/n)^n : ℝ) : ℂ)) from by fun_prop).locallyIntegrable.indicator
    measurableSet_Ioc)

lemma gammaApproxKernel_mellin_derivative (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    MellinConvergent (fun t : ℝ => Real.log t • gammaApproxKernel n t) s ∧
      HasDerivAt (mellin (gammaApproxKernel n))
        (mellin (fun t : ℝ => Real.log t • gammaApproxKernel n t) s) s := by
  have htop : gammaApproxKernel n =O[atTop] (fun t : ℝ => t^(-(s.re+1))) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_gt_atTop (n : ℝ)] with t ht
    rw [gammaApproxKernel,indicator_of_notMem (notMem_Ioc_of_gt ht),norm_zero]
    positivity
  have hbot : gammaApproxKernel n =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t^(-(0 : ℝ))) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    have ht0 : 0 < t := ht
    have hb := gammaApproxKernel_norm_bound n t ht
    have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    simpa only [neg_zero,Real.rpow_zero,norm_one,one_mul] using hb.trans he
  exact mellin_hasDerivAt_of_isBigO_rpow
    ((gammaApproxKernel_locallyIntegrable n).locallyIntegrableOn (Ioi 0))
    htop (by linarith) hbot hs

lemma GammaSeq_eq_mellin_kernel (n : ℕ) (hn : n ≠ 0) (s : ℂ) (hs : 0 < s.re) :
    GammaSeq s n=mellin (gammaApproxKernel n) s := by
  rw [GammaSeq_eq_approx_Gamma_integral hs hn,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ n)]
  unfold mellin gammaApproxKernel
  have he : (fun t : ℝ => (t : ℂ)^(s-1) •
      (Ioc (0 : ℝ) (n : ℝ)).indicator (fun t : ℝ => (((1-t/n)^n : ℝ) : ℂ)) t)=
      (Ioc (0 : ℝ) (n : ℝ)).indicator (fun t : ℝ =>
        (((1-t/n)^n : ℝ) : ℂ)*(t : ℂ)^(s-1)) := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ) n <;> simp [ht,smul_eq_mul,mul_comm]
  rw [he,integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]

lemma GammaSeq_hasDerivAt_integral (n : ℕ) (hn : n ≠ 0) (s : ℂ) (hs : 0 < s.re) :
    HasDerivAt (fun z : ℂ => GammaSeq z n)
      (mellin (fun t : ℝ => Real.log t • gammaApproxKernel n t) s) s := by
  apply (gammaApproxKernel_mellin_derivative n s hs).2.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
  exact GammaSeq_eq_mellin_kernel n hn z hz

lemma exp_neg_log_mellin_convergent (s : ℂ) (hs : 0 < s.re) :
    MellinConvergent (fun t : ℝ => Real.log t • (Real.exp (-t) : ℂ)) s := by
  have htop : (fun t : ℝ => (Real.exp (-t) : ℂ)) =O[atTop]
      (fun t : ℝ => t^(-(s.re+1))) := by
    rw [← isBigO_norm_left]
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    simpa only [neg_mul,one_mul] using
      (isLittleO_exp_neg_mul_rpow_atTop (a := 1) (by norm_num) (-(s.re+1))).isBigO
  have hbot : (fun t : ℝ => (Real.exp (-t) : ℂ)) =O[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t^(-(0 : ℝ))) := by
    simp only [neg_zero,Real.rpow_zero]
    have hlim : Tendsto (fun t : ℝ => (Real.exp (-t) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
      simpa using ((show Continuous (fun t : ℝ => (Real.exp (-t) : ℂ)) from by fun_prop).tendsto
        (0 : ℝ)).mono_left nhdsWithin_le_nhds
    exact isBigO_const_of_tendsto hlim (one_ne_zero : (1 : ℝ) ≠ 0)
  exact (mellin_hasDerivAt_of_isBigO_rpow
    ((show Continuous (fun t : ℝ => (Real.exp (-t) : ℂ)) from by fun_prop).continuousOn.locallyIntegrableOn
      measurableSet_Ioi) htop (by linarith) hbot hs).1

lemma gamma_log_weight_integrable (σ : ℝ) (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ => t^(σ-1)*|Real.log t| * Real.exp (-t)) (Ioi (0 : ℝ)) := by
  have hi := (exp_neg_log_mellin_convergent (σ : ℂ) (by simpa using hσ)).norm
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [norm_smul,Complex.norm_cpow_eq_rpow_re_of_pos ht,Complex.sub_re,
    Complex.ofReal_re,Complex.one_re,Real.norm_eq_abs,Complex.norm_real,
    abs_of_pos (Real.exp_pos _)]
  ring

lemma gammaApproxKernel_tendsto (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => gammaApproxKernel n t) atTop (𝓝 (Real.exp (-t) : ℂ)) := by
  have hh : Tendsto (fun n : ℕ => (((1-t/n)^n : ℝ) : ℂ)) atTop (𝓝 (Real.exp (-t) : ℂ)) := by
    apply (continuous_ofReal.tendsto _).comp
    convert Real.tendsto_one_add_div_pow_exp (-t) using 1
    ext n
    rw [neg_div,← sub_eq_add_neg]
  apply hh.congr'
  filter_upwards [eventually_ge_atTop ⌈t⌉₊] with n hn
  rw [Nat.ceil_le] at hn
  exact (indicator_of_mem (show t ∈ Ioc (0 : ℝ) n from ⟨ht,hn⟩)
    (fun t : ℝ => (((1-t/n)^n : ℝ) : ℂ))).symm

lemma gammaApprox_log_mellin_tendsto (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => mellin (fun t : ℝ => Real.log t • gammaApproxKernel n t) s)
      atTop (𝓝 (mellin (fun t : ℝ => Real.log t • (Real.exp (-t) : ℂ)) s)) := by
  let F : ℕ → ℝ → ℂ := fun n t => (t : ℂ)^(s-1) • (Real.log t • gammaApproxKernel n t)
  have hi (n : ℕ) : IntegrableOn (F n) (Ioi (0 : ℝ)) :=
    (gammaApproxKernel_mellin_derivative n s hs).1
  have hlim : ∀ᵐ t : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      Tendsto (fun n => F n t) atTop
        (𝓝 ((t : ℂ)^(s-1) • (Real.log t • (Real.exp (-t) : ℂ)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact ((gammaApproxKernel_tendsto t ht).const_smul (Real.log t)).const_smul ((t : ℂ)^(s-1))
  have hb (n : ℕ) : ∀ᵐ t : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      ‖F n t‖ ≤ t^(s.re-1)*|Real.log t| * Real.exp (-t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    dsimp only [F]
    rw [norm_smul,norm_smul,Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp only [Complex.sub_re,Complex.one_re,Real.norm_eq_abs]
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left (gammaApproxKernel_norm_bound n t ht)
      (mul_nonneg (Real.rpow_nonneg (show (0 : ℝ) ≤ t from le_of_lt ht) _) (abs_nonneg _))
  exact tendsto_integral_of_dominated_convergence _ (fun n => (hi n).1)
    (gamma_log_weight_integrable s.re hs) hb hlim

lemma Gamma_hasDerivAt_log_mellin (s : ℂ) (hs : 0 < s.re) :
    HasDerivAt Gamma (mellin (fun t : ℝ => Real.log t • (Real.exp (-t) : ℂ)) s) s := by
  have hd : HasDerivAt GammaIntegral
      (mellin (fun t : ℝ => Real.log t • (Real.exp (-t) : ℂ)) s) s := by
    convert hasDerivAt_GammaIntegral hs using 1
    unfold mellin
    congr 1
  apply hd.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
  exact Gamma_eq_integral hz

lemma GammaSeq_deriv_tendsto (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => deriv (fun z : ℂ => GammaSeq z n) s) atTop (𝓝 (deriv Gamma s)) := by
  rw [(Gamma_hasDerivAt_log_mellin s hs).deriv]
  apply (gammaApprox_log_mellin_tendsto s hs).congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (GammaSeq_hasDerivAt_integral n hn s hs).deriv.symm

lemma GammaSeq_logDeriv_tendsto (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => logDeriv (fun z : ℂ => GammaSeq z n) s) atTop (𝓝 (logDeriv Gamma s)) := by
  have hG : Gamma s ≠ 0 := Gamma_ne_zero (fun m => by
    intro he
    have hr := congrArg Complex.re he
    simp only [neg_re,natCast_re] at hr
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith)
  exact (GammaSeq_deriv_tendsto s hs).div (GammaSeq_tendsto_Gamma s) hG

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter Complex
open scoped Topology

namespace Helfgott

lemma GammaSeq_logDeriv_formula (n : ℕ) (hn : n ≠ 0) (s : ℂ) (hs : 0 < s.re) :
    logDeriv (fun z : ℂ => GammaSeq z n) s=
      log (n : ℂ)-∑ j ∈ Finset.range (n+1),(s+(j : ℂ))⁻¹ := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hcp : (n : ℂ)^s ≠ 0 := cpow_ne_zero_iff.mpr (.inl hnC)
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have he (j : ℕ) : s+(j : ℂ) ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp only [add_re,natCast_re,zero_re] at hr
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hd : DifferentiableAt ℂ (fun z : ℂ => (n : ℂ)^z) s :=
    by simpa only [id_eq] using ((hasDerivAt_id s).const_cpow (.inl hnC)).differentiableAt
  have hdp : DifferentiableAt ℂ (fun z : ℂ => ∏ j ∈ Finset.range (n+1),(z+(j : ℂ))) s := by
    fun_prop
  change logDeriv (fun z : ℂ => (n : ℂ)^z*n.factorial/
    ∏ j ∈ Finset.range (n+1),(z+(j : ℂ))) s=_
  rw [logDeriv_div (f := fun z : ℂ => (n : ℂ)^z*n.factorial)
    (g := fun z : ℂ => ∏ j ∈ Finset.range (n+1),(z+(j : ℂ))) s (mul_ne_zero hcp hf)
    (Finset.prod_ne_zero_iff.mpr (fun j hj => he j)) (hd.mul_const _) hdp,
    logDeriv_mul_const (f := fun z : ℂ => (n : ℂ)^z) s (n.factorial : ℂ) hf]
  have hc : logDeriv (fun z : ℂ => (n : ℂ)^z) s=log (n : ℂ) := by
    rw [logDeriv_apply]
    have hd' := (hasDerivAt_id s).const_cpow (.inl hnC)
    have hder : deriv (fun z : ℂ => (n : ℂ)^z) s=(n : ℂ)^s*log (n : ℂ) := by
      simpa only [id_eq,mul_one] using hd'.deriv
    rw [hder]
    exact mul_div_cancel_left₀ _ hcp
  rw [hc,logDeriv_prod (s := Finset.range (n+1)) (f := fun (j : ℕ) (z : ℂ) => z+(j : ℂ))
    (fun j hj => he j) (by intro j hj; fun_prop)]
  simp [logDeriv_apply]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter Complex
open scoped Topology

namespace Helfgott

lemma finite_inverse_square_bound (n : ℕ) :
    (∑ j ∈ Finset.range n,1/((j : ℝ)+1)^2) ≤ 2-2/((n : ℝ)+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    calc
      _ ≤ (2-2/((n : ℝ)+1))+1/((n : ℝ)+1)^2 := add_le_add ih le_rfl
      _ ≤ 2-2/((n : ℝ)+1+1) := by
        have h1 : 0 < (n : ℝ)+1 := by positivity
        have h2 : 0 < (n : ℝ)+1+1 := by positivity
        field_simp
        nlinarith [Nat.cast_nonneg (α := ℝ) n]

lemma harmonic_log_norm_bound (n : ℕ) (hn : n ≠ 0) :
    ‖log (n : ℂ)-(harmonic n : ℂ)‖ ≤ 1 := by
  have hp : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlow : Real.log (n : ℝ) ≤ (harmonic n : ℝ) := by
    exact (Real.log_le_log hp (by exact_mod_cast Nat.le_succ n)).trans (log_add_one_le_harmonic n)
  have hu := harmonic_le_one_add_log n
  rw [← Complex.natCast_log]
  have he : (Real.log (n : ℝ) : ℂ)-(harmonic n : ℂ)=
      ((Real.log (n : ℝ)-(harmonic n : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [he,Complex.norm_real]
  rw [Real.norm_eq_abs,abs_of_nonpos (by linarith : Real.log (n : ℝ)-(harmonic n : ℝ) ≤ 0)]
  linarith

lemma reciprocal_shift_difference_bound (s : ℂ) (hs : 0 < s.re) (j : ℕ) :
    ‖(((j : ℂ)+1)⁻¹-(s+((j : ℂ)+1))⁻¹)‖ ≤ ‖s‖/((j : ℝ)+1)^2 := by
  have hj : (0 : ℝ)<(j : ℝ)+1 := by positivity
  have hjC : (j : ℂ)+1 ≠ 0 := by exact_mod_cast hj.ne'
  have hsC : s+((j : ℂ)+1) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [add_re,natCast_re,one_re,zero_re] at hr
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have he : ((j : ℂ)+1)⁻¹-(s+((j : ℂ)+1))⁻¹=
      s/(((j : ℂ)+1)*(s+((j : ℂ)+1))) := by field_simp; ring
  rw [he,norm_div,norm_mul]
  have hnorm : ‖(j : ℂ)+1‖=(j : ℝ)+1 := by
    rw [← Complex.ofReal_natCast,← Complex.ofReal_one,← Complex.ofReal_add,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hj]
  rw [hnorm]
  have hd : (j : ℝ)+1 ≤ ‖s+((j : ℂ)+1)‖ := by
    calc
      _ ≤ (s+((j : ℂ)+1)).re := by simp; linarith
      _ ≤ _ := Complex.re_le_norm _
  rw [pow_two]
  gcongr

lemma GammaSeq_logDeriv_harmonic_split (n : ℕ) (hn : n ≠ 0) (s : ℂ) (hs : 0 < s.re) :
    logDeriv (fun z : ℂ => GammaSeq z n) s=log (n : ℂ)-(harmonic n : ℂ)-s⁻¹+
      ∑ j ∈ Finset.range n,(((j : ℂ)+1)⁻¹-(s+((j : ℂ)+1))⁻¹) := by
  have hH : (harmonic n : ℂ)=∑ j ∈ Finset.range n,((j : ℂ)+1)⁻¹ := by
    simp [harmonic]
  rw [GammaSeq_logDeriv_formula n hn s hs,hH,Finset.sum_range_succ']
  simp only [Nat.cast_zero,add_zero,Nat.cast_add,Nat.cast_one,Finset.sum_sub_distrib]
  ring

lemma GammaSeq_logDeriv_norm_bound (n : ℕ) (hn : n ≠ 0) (s : ℂ) (hs : 0 < s.re) :
    ‖logDeriv (fun z : ℂ => GammaSeq z n) s‖ ≤ 1+1/s.re+2*‖s‖ := by
  have hi : ‖s⁻¹‖ ≤ 1/s.re := by
    rw [norm_inv]
    simpa only [one_div] using one_div_le_one_div_of_le hs (Complex.re_le_norm s)
  have hsum : ‖∑ j ∈ Finset.range n,(((j : ℂ)+1)⁻¹-(s+((j : ℂ)+1))⁻¹)‖ ≤ 2*‖s‖ := by
    calc
      _ ≤ ∑ j ∈ Finset.range n,‖(((j : ℂ)+1)⁻¹-(s+((j : ℂ)+1))⁻¹)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range n,‖s‖/((j : ℝ)+1)^2 :=
        Finset.sum_le_sum (fun j hj => reciprocal_shift_difference_bound s hs j)
      _ = ‖s‖*(∑ j ∈ Finset.range n,1/((j : ℝ)+1)^2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ ‖s‖*2 := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg s)
        exact (finite_inverse_square_bound n).trans (sub_le_self _ (by positivity))
      _ = _ := by ring
  rw [GammaSeq_logDeriv_harmonic_split n hn s hs]
  calc
    _ ≤ ‖log (n : ℂ)-(harmonic n : ℂ)-s⁻¹‖+
        ‖∑ j ∈ Finset.range n,(((j : ℂ)+1)⁻¹-(s+((j : ℂ)+1))⁻¹)‖ := norm_add_le _ _
    _ ≤ ‖log (n : ℂ)-(harmonic n : ℂ)‖+‖s⁻¹‖+2*‖s‖ :=
      add_le_add (norm_sub_le _ _) hsum
    _ ≤ _ := by linarith [harmonic_log_norm_bound n hn]

theorem Gamma_logDeriv_linear_bound (s : ℂ) (hs : 0 < s.re) :
    ‖deriv Gamma s/Gamma s‖ ≤ 1+1/s.re+2*‖s‖ := by
  apply le_of_tendsto (GammaSeq_logDeriv_tendsto s hs).norm
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact GammaSeq_logDeriv_norm_bound n hn s hs

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter Complex
open scoped Topology

namespace Helfgott

lemma GammaR_logDeriv_formula (s : ℂ) (hs : ∀ m : ℕ,s/2 ≠ -(m : ℂ)) :
    logDeriv Gammaℝ s= -log (Real.pi : ℂ)/2+(logDeriv Gamma (s/2))/2 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hp : (Real.pi : ℂ)^(-s/2) ≠ 0 := cpow_ne_zero_iff.mpr (.inl hπ)
  have hG := Gamma_ne_zero hs
  have hdP := ((hasDerivAt_id s).neg.div_const 2).const_cpow (.inl hπ)
  have hdG := (differentiableAt_Gamma (s/2) hs).comp s
    (show DifferentiableAt ℂ (fun z : ℂ => z/2) s from by fun_prop)
  change logDeriv (fun z : ℂ => (Real.pi : ℂ)^(-z/2)*Gamma (z/2)) s=_
  rw [logDeriv_mul (f := fun z : ℂ => (Real.pi : ℂ)^(-z/2))
    (g := fun z : ℂ => Gamma (z/2)) s hp hG hdP.differentiableAt hdG]
  have heP : logDeriv (fun z : ℂ => (Real.pi : ℂ)^(-z/2)) s= -log (Real.pi : ℂ)/2 := by
    rw [logDeriv_apply]
    have hder : deriv (fun z : ℂ => (Real.pi : ℂ)^(-z/2)) s=
        (Real.pi : ℂ)^(-s/2)*log (Real.pi : ℂ)*(-1/2) := by
      simpa only [Pi.neg_apply,id_eq] using hdP.deriv
    rw [hder]
    field_simp
  rw [heP]
  change -log (Real.pi : ℂ)/2+logDeriv (Gamma ∘ (fun z : ℂ => z/2)) s=_
  rw [logDeriv_comp (f := Gamma) (g := fun z : ℂ => z/2) (differentiableAt_Gamma (s/2) hs)
    (show DifferentiableAt ℂ (fun z : ℂ => z/2) s from by fun_prop)]
  simp [div_eq_mul_inv]

lemma GammaR_positive_logDeriv_bound (s : ℂ) (hs : 0 < s.re) :
    ‖logDeriv Gammaℝ s‖ ≤ |Real.log Real.pi|/2+1/2+1/s.re+‖s‖/2 := by
  have hsp : 0 < (s/2).re := by simp; linarith
  have hne : ∀ m : ℕ,s/2 ≠ -(m : ℂ) := by
    intro m he
    have hr := congrArg Complex.re he
    simp only [neg_re,natCast_re] at hr
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hb := Gamma_logDeriv_linear_bound (s/2) hsp
  change ‖logDeriv Gamma (s/2)‖ ≤ 1+1/(s/2).re+2*‖s/2‖ at hb
  rw [GammaR_logDeriv_formula s hne]
  have hlog : ‖log (Real.pi : ℂ)‖=|Real.log Real.pi| := by
    rw [← Complex.ofReal_log Real.pi_pos.le,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ ‖-log (Real.pi : ℂ)/2‖+‖logDeriv Gamma (s/2)/2‖ := norm_add_le _ _
    _ = |Real.log Real.pi|/2+‖logDeriv Gamma (s/2)‖/2 := by simp [norm_div,hlog]
    _ ≤ |Real.log Real.pi|/2+(1+1/(s/2).re+2*‖s/2‖)/2 := by
      gcongr
    _ = _ := by simp [norm_div]; ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter Complex
open scoped Topology

namespace Helfgott

lemma GammaR_negative_half_logDeriv_bound (s : ℂ) (hσ : s.re= -1/2) :
    ‖logDeriv Gammaℝ s‖ ≤ |Real.log Real.pi|/2+4+|s.im|/2 := by
  let z := s/2
  have hr : z.re= -1/4 := by dsimp [z]; simp [hσ]; norm_num
  have hrp : (z+1).re=3/4 := by simp [hr]; norm_num
  have hne : ∀ m : ℕ,z ≠ -(m : ℂ) := by
    intro m he
    have hm := congrArg Complex.re he
    rw [hr] at hm
    simp only [neg_re,natCast_re] at hm
    rcases Nat.eq_zero_or_pos m with rfl | hp
    · norm_num at hm
    · have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hp
      linarith
  have hb := Gamma_logDeriv_linear_bound (z+1) (by rw [hrp]; norm_num)
  change ‖logDeriv Gamma (z+1)‖ ≤ 1+1/(z+1).re+2*‖z+1‖ at hb
  rw [hrp] at hb
  have hh := Complex.digamma_apply_add_one z hne
  change logDeriv Gamma (z+1)=logDeriv Gamma z+z⁻¹ at hh
  have he : logDeriv Gamma z=logDeriv Gamma (z+1)-z⁻¹ := eq_sub_of_add_eq hh.symm
  have hz : (1/4 : ℝ) ≤ ‖z‖ := by
    have ha := Complex.abs_re_le_norm z
    norm_num [hr] at ha
    exact ha
  have hi : ‖z⁻¹‖ ≤ 4 := by
    rw [norm_inv]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1/4) hz
    norm_num [one_div] at h
    exact h
  have hn : ‖z+1‖ ≤ 3/4+|s.im|/2 := by
    have h := Complex.norm_le_abs_re_add_abs_im (z+1)
    simpa [hrp,z,abs_div] using h
  have hzg : ‖logDeriv Gamma z‖ ≤ 8+|s.im| := by
    rw [he]
    have h := norm_sub_le (logDeriv Gamma (z+1)) z⁻¹
    norm_num at hb
    linarith
  rw [GammaR_logDeriv_formula s hne]
  have hlog : ‖log (Real.pi : ℂ)‖=|Real.log Real.pi| := by
    rw [← Complex.ofReal_log Real.pi_pos.le,Complex.norm_real,Real.norm_eq_abs]
  have htri := norm_add_le (-log (Real.pi : ℂ)/2) (logDeriv Gamma z/2)
  simp only [norm_div,norm_neg,Complex.norm_ofNat,hlog] at htri
  linarith

lemma GammaR_positive_small_logDeriv_bound (s : ℂ)
    (hσ : s.re=1/2 ∨ s.re=3/2 ∨ s.re=5/2) :
    ‖logDeriv Gammaℝ s‖ ≤ |Real.log Real.pi|/2+3+|s.im|/2 := by
  rcases hσ with hσ | hσ | hσ
  all_goals
    have hb := GammaR_positive_logDeriv_bound s (by rw [hσ]; norm_num)
    have hn := Complex.norm_le_abs_re_add_abs_im s
    rw [hσ] at hb hn
    norm_num at hb hn
    linarith

lemma gammaFactor_negative_half_logDeriv_bound (q : ℕ) (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hσ : s.re= -1/2) :
    ‖logDeriv χ.gammaFactor s‖ ≤ |Real.log Real.pi|/2+4+|s.im|/2 := by
  rcases χ.even_or_odd with he | ho
  · have heq : χ.gammaFactor=Gammaℝ := funext (fun z => he.gammaFactor_def z)
    rw [heq]
    exact GammaR_negative_half_logDeriv_bound s hσ
  · have heq : χ.gammaFactor=(fun z : ℂ => Gammaℝ (z+1)) := funext (fun z => ho.gammaFactor_def z)
    rw [heq,logDeriv_apply,deriv_comp_add_const]
    change ‖logDeriv Gammaℝ (s+1)‖ ≤ _
    have hb := GammaR_positive_small_logDeriv_bound (s+1) (.inl (by simp [hσ]; norm_num))
    simp only [add_im,one_im,add_zero] at hb
    linarith

lemma gammaFactor_three_halves_logDeriv_bound (q : ℕ) (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hσ : s.re=3/2) :
    ‖logDeriv χ.gammaFactor s‖ ≤ |Real.log Real.pi|/2+3+|s.im|/2 := by
  rcases χ.even_or_odd with he | ho
  · have heq : χ.gammaFactor=Gammaℝ := funext (fun z => he.gammaFactor_def z)
    rw [heq]
    exact GammaR_positive_small_logDeriv_bound s (.inr (.inl hσ))
  · have heq : χ.gammaFactor=(fun z : ℂ => Gammaℝ (z+1)) := funext (fun z => ho.gammaFactor_def z)
    rw [heq,logDeriv_apply,deriv_comp_add_const]
    change ‖logDeriv Gammaℝ (s+1)‖ ≤ _
    have hb := GammaR_positive_small_logDeriv_bound (s+1) (.inr (.inr (by simp [hσ]; norm_num)))
    simpa only [add_im,one_im,add_zero] using hb

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex

namespace Helfgott

lemma gammaFactor_ne_zero_negative_strip (q : ℕ) (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : -1 < s.re) (hs0 : s.re < 0) : χ.gammaFactor s ≠ 0 := by
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def]
    intro hz
    obtain ⟨n,hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hz
    have hr := congrArg Complex.re hn
    norm_num at hr
    by_cases h : n=0
    · simp [h] at hr
      linarith
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h)
      linarith
  · rw [ho.gammaFactor_def]
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [add_re,one_re]
    linarith

lemma primitive_LFunction_ne_zero_negative_strip (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive)
    (s : ℂ) (hs : -1 < s.re) (hs0 : s.re < 0) : χ.LFunction s ≠ 0 := by
  have hright : 1 < (1-s).re := by simp only [sub_re,one_re]; linarith
  have hL : (χ⁻¹).LFunction (1-s) ≠ 0 := by
    rw [DirichletCharacter.LFunction_eq_LSeries _ hright]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re _ hright
  have hsne : s ≠ 0 := by intro h; simp [h] at hs0
  have hrne : 1-s ≠ 0 := by intro h; rw [h] at hright; norm_num at hright
  have hC : (χ⁻¹).completedLFunction (1-s) ≠ 0 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor _ _ (.inl hrne)] at hL
    exact (div_ne_zero_iff.mp hL).1
  have hpi : (χ⁻¹).IsPrimitive := by
    change (χ⁻¹).conductor=q
    rw [DirichletCharacter.conductor_inv]
    exact hp
  have he := hpi.completedLFunction_one_sub s
  rw [inv_inv] at he
  rw [he] at hC
  have hc : χ.completedLFunction s ≠ 0 := right_ne_zero_of_mul hC
  rw [χ.LFunction_eq_completed_div_gammaFactor s (.inl hsne)]
  exact div_ne_zero hc (gammaFactor_ne_zero_negative_strip q χ s hs hs0)

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set Complex
open scoped Topology

namespace Helfgott

lemma gammaFactor_logDeriv_from_LFunction (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ)
    (hs : s ≠ 0) (hL : χ.LFunction s ≠ 0) :
    logDeriv χ.gammaFactor s=logDeriv χ.completedLFunction s-logDeriv χ.LFunction s := by
  have hdL := DirichletCharacter.differentiable_LFunction hχ
  have hdC := DirichletCharacter.differentiable_completedLFunction hχ
  have hCs : χ.completedLFunction s ≠ 0 := by
    rw [χ.LFunction_eq_completed_div_gammaFactor s (.inl hs)] at hL
    exact (div_ne_zero_iff.mp hL).1
  have he : χ.gammaFactor =ᶠ[𝓝 s] (fun w => χ.completedLFunction w/χ.LFunction w) := by
    filter_upwards [hdL.continuous.continuousAt.eventually_ne hL,
      (continuousAt_id : ContinuousAt (fun w : ℂ => w) s).eventually_ne hs] with w hLw hw
    have hrel := χ.LFunction_eq_completed_div_gammaFactor w (.inl hw)
    have hg : χ.gammaFactor w ≠ 0 := by rw [hrel] at hLw; exact (div_ne_zero_iff.mp hLw).2
    apply (eq_div_iff hLw).mpr
    rw [mul_comm]
    exact ((div_eq_iff hg).mp hrel.symm).symm
  rw [(logDeriv_congr_nhds he).eq_of_nhds,
    logDeriv_div s hCs hL (hdC s) (hdL s)]

lemma primitive_completed_logDeriv_reflection (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    (s : ℂ) (hs : -1 < s.re) (hs0 : s.re < 0) :
    logDeriv χ.completedLFunction s+
      logDeriv (χ⁻¹).completedLFunction (1-s)= -log (q : ℂ) := by
  have hχi : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ
    simpa using congrArg (fun χ : DirichletCharacter ℂ q => χ⁻¹) h
  have hpi : (χ⁻¹).IsPrimitive := by
    change (χ⁻¹).conductor=q
    rw [DirichletCharacter.conductor_inv]
    exact hp
  have hright : 1 < (1-s).re := by simp only [sub_re,one_re]; linarith
  have hLs := primitive_LFunction_ne_zero_negative_strip q χ hp s hs hs0
  have hLr := DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ⁻¹) (.inl hχi) hright.le
  have hsne : s ≠ 0 := by intro he; simp [he] at hs0
  have hrne : 1-s ≠ 0 := by intro he; rw [he] at hright; norm_num at hright
  have hCs : χ.completedLFunction s ≠ 0 := by
    rw [χ.LFunction_eq_completed_div_gammaFactor s (.inl hsne)] at hLs
    exact (div_ne_zero_iff.mp hLs).1
  have hCr : (χ⁻¹).completedLFunction (1-s) ≠ 0 := by
    rw [(χ⁻¹).LFunction_eq_completed_div_gammaFactor (1-s) (.inl hrne)] at hLr
    exact (div_ne_zero_iff.mp hLr).1
  let P : ℂ → ℂ := fun w => (q : ℂ)^(w-1/2)
  let ε : ℂ := (χ⁻¹).rootNumber
  have hE : (fun w : ℂ => (χ⁻¹).completedLFunction (1-w))=
      (fun w : ℂ => P w*ε*χ.completedLFunction w) := by
    funext w
    simpa only [inv_inv,P,ε] using hpi.completedLFunction_one_sub w
  have hε : ε ≠ 0 := by
    have he := congrFun hE s
    rw [he] at hCr
    exact right_ne_zero_of_mul (left_ne_zero_of_mul hCr)
  have hP : P s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (.inl (by exact_mod_cast NeZero.ne q))
  have hdP : DifferentiableAt ℂ P s :=
    (differentiableAt_id.sub_const (1/2 : ℂ)).const_cpow (.inl (by exact_mod_cast NeZero.ne q))
  have hdC := DirichletCharacter.differentiable_completedLFunction hχ
  have hdCi := DirichletCharacter.differentiable_completedLFunction hχi
  have hlog := congrArg (fun F : ℂ → ℂ => logDeriv F s) hE
  have hcomp : logDeriv (fun w : ℂ => (χ⁻¹).completedLFunction (1-w)) s=
      -logDeriv (χ⁻¹).completedLFunction (1-s) := by
    change logDeriv ((χ⁻¹).completedLFunction ∘ (fun w : ℂ => 1-w)) s = _
    rw [logDeriv_comp (hdCi (1-s)) ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id)]
    simp
  have hpLog : logDeriv P s=log (q : ℂ) := by
    rw [logDeriv_apply]
    have hd := Complex.deriv_const_cpow (x := s) (differentiableAt_id.sub_const (1/2 : ℂ)) (q : ℂ)
    have hd' : deriv P s=log (q : ℂ)*P s := by simpa [P] using hd
    rw [hd']
    exact mul_div_cancel_right₀ _ hP
  rw [hcomp,logDeriv_mul (f := fun w : ℂ => P w*ε) (g := χ.completedLFunction)
    s (mul_ne_zero hP hε) hCs
    (hdP.mul_const ε) (hdC s),logDeriv_mul_const (f := P) s ε hε,hpLog] at hlog
  linear_combination -hlog

theorem primitive_negative_strip_logDeriv_prime_series
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive)
    (hχ : χ ≠ 1) (s : ℂ) (hs : -1 < s.re) (hs0 : s.re < 0) :
    LSeriesSummable (fun n : ℕ => χ⁻¹ n*(ArithmeticFunction.vonMangoldt n : ℂ)) (1-s) ∧
      -deriv χ.LFunction s/χ.LFunction s = log (q : ℂ)+
        deriv χ.gammaFactor s/χ.gammaFactor s+
        deriv (χ⁻¹).gammaFactor (1-s)/(χ⁻¹).gammaFactor (1-s)-
        LSeries (fun n : ℕ => χ⁻¹ n*(ArithmeticFunction.vonMangoldt n : ℂ)) (1-s) := by
  have hχi : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ
    simpa using congrArg (fun χ : DirichletCharacter ℂ q => χ⁻¹) h
  have hr : 1 < (1-s).re := by simp only [sub_re,one_re]; linarith
  have hec : ((fun n : ℕ => χ⁻¹ n)*(fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)))=
      (fun n : ℕ => χ⁻¹ n*(ArithmeticFunction.vonMangoldt n : ℂ)) := by ext n; rfl
  refine ⟨?_,?_⟩
  · simpa only [hec] using (χ⁻¹).LSeriesSummable_twist_vonMangoldt hr
  · have hLs := primitive_LFunction_ne_zero_negative_strip q χ hp s hs hs0
    have hLr := DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ⁻¹) (.inl hχi) hr.le
    have hsne : s ≠ 0 := by intro he; simp [he] at hs0
    have hrne : 1-s ≠ 0 := by intro he; rw [he] at hr; norm_num at hr
    have hg := gammaFactor_logDeriv_from_LFunction q χ hχ s hsne hLs
    have hgi := gammaFactor_logDeriv_from_LFunction q (χ⁻¹) hχi (1-s) hrne hLr
    have href := primitive_completed_logDeriv_reflection q χ hp hχ s hs hs0
    have hseries := (χ⁻¹).LSeries_twist_vonMangoldt_eq hr
    rw [← (χ⁻¹).deriv_LFunction_eq_deriv_LSeries hr,← (χ⁻¹).LFunction_eq_LSeries hr] at hseries
    simp only [hec] at hseries
    simp only [logDeriv_apply] at hg hgi href
    linear_combination -hg-hgi-href+hseries

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set Complex

namespace Helfgott

lemma tsum_nat_rpow_five_quarters_le : (∑' n : ℕ,(n : ℝ)^(-(5/4 : ℝ))) ≤ 5 := by
  have hs : Summable (fun n : ℕ => (n : ℝ)^(-(5/4 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have ha : AntitoneOn (fun x : ℝ => x^(-(5/4 : ℝ))) (Ici (1 : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num : -(5/4 : ℝ) ≤ 0)).mono
      (by intro x hx; exact lt_of_lt_of_le zero_lt_one (show (1 : ℝ) ≤ x from hx))
  have ht := AntitoneOn.tsum_comp_add_le_integral 1 (by simpa using ha)
    (integrableOn_Ioi_rpow_of_lt (by norm_num : -(5/4 : ℝ)< -1) (by norm_num))
    (fun x hx => Real.rpow_nonneg (le_of_lt (show (0 : ℝ)<x from by
      have hx' : ((1 : ℕ) : ℝ)<x := hx
      norm_num at hx'
      linarith)) _)
  rw [integral_Ioi_rpow_of_lt (by norm_num : -(5/4 : ℝ)< -1) (by norm_num)] at ht
  norm_num at ht
  have hs1 : Summable (fun n : ℕ => ((n+1 : ℕ) : ℝ)^(-(5/4 : ℝ))) :=
    (summable_nat_add_iff 1).mpr hs
  rw [hs.tsum_eq_zero_add,hs1.tsum_eq_zero_add]
  norm_num
  linarith [ht]

lemma dirichlet_prime_term_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 3/2 ≤ s.re) (n : ℕ) :
    ‖LSeries.term (fun m : ℕ => χ m*(ArithmeticFunction.vonMangoldt m : ℂ)) s n‖ ≤
      4*(n : ℝ)^(-(5/4 : ℝ)) := by
  by_cases hn : n=0
  · subst n
    simp
  have hp : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hv : ArithmeticFunction.vonMangoldt n ≤ 4*(n : ℝ)^(1/4 : ℝ) := by
    have hl := Real.log_le_rpow_div hp.le (by norm_num : (0 : ℝ)<1/4)
    exact ArithmeticFunction.vonMangoldt_le_log.trans (by nlinarith [hl])
  rw [LSeries.norm_term_eq,if_neg hn,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  calc
    _ ≤ (1*(4*(n : ℝ)^(1/4 : ℝ)))/(n : ℝ)^s.re := by
      gcongr
      exact χ.norm_le_one n
    _ ≤ (4*(n : ℝ)^(1/4 : ℝ))/(n : ℝ)^(3/2 : ℝ) := by
      simp only [one_mul]
      gcongr
    _ = _ := by
      rw [mul_div_assoc,← Real.rpow_sub hp]
      norm_num

theorem dirichlet_LFunction_right_logDeriv_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 3/2 ≤ s.re) :
    LSeriesSummable (fun n : ℕ => χ n*(ArithmeticFunction.vonMangoldt n : ℂ)) s ∧
      ‖-deriv χ.LFunction s/χ.LFunction s‖ ≤ 20 := by
  have hs1 : 1 < s.re := by linarith
  have hec : ((fun n : ℕ => χ n)*(fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)))=
      (fun n : ℕ => χ n*(ArithmeticFunction.vonMangoldt n : ℂ)) := by ext n; rfl
  have hsum : LSeriesSummable (fun n : ℕ => χ n*(ArithmeticFunction.vonMangoldt n : ℂ)) s := by
    simpa only [hec] using χ.LSeriesSummable_twist_vonMangoldt hs1
  refine ⟨hsum,?_⟩
  have hid := χ.LSeries_twist_vonMangoldt_eq hs1
  rw [← χ.deriv_LFunction_eq_deriv_LSeries hs1,← χ.LFunction_eq_LSeries hs1] at hid
  simp only [hec] at hid
  rw [← hid]
  change ‖∑' n : ℕ,LSeries.term (fun m : ℕ => χ m*(ArithmeticFunction.vonMangoldt m : ℂ)) s n‖ ≤ 20
  calc
    _ ≤ ∑' n : ℕ,‖LSeries.term (fun m : ℕ => χ m*(ArithmeticFunction.vonMangoldt m : ℂ)) s n‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ,4*(n : ℝ)^(-(5/4 : ℝ)) := by
      exact Summable.tsum_le_tsum (fun n => dirichlet_prime_term_bound q χ s hs n)
        hsum.norm ((Real.summable_nat_rpow.mpr (by norm_num : -(5/4 : ℝ)< -1)).mul_left 4)
    _ ≤ 20 := by
      rw [tsum_mul_left]
      linarith [tsum_nat_rpow_five_quarters_le]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter Complex
open scoped Topology

namespace Helfgott

lemma gammaFactor_logDeriv_from_LFunction_local (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hL : χ.LFunction s ≠ 0) :
    logDeriv χ.gammaFactor s=logDeriv χ.completedLFunction s-logDeriv χ.LFunction s := by
  have hdL := χ.differentiableAt_LFunction s (.inl hs1)
  have hdC := χ.differentiableAt_completedLFunction s (.inl hs0) (.inl hs1)
  have hCs : χ.completedLFunction s ≠ 0 := by
    rw [χ.LFunction_eq_completed_div_gammaFactor s (.inl hs0)] at hL
    exact (div_ne_zero_iff.mp hL).1
  have he : χ.gammaFactor =ᶠ[𝓝 s] (fun w => χ.completedLFunction w/χ.LFunction w) := by
    filter_upwards [hdL.continuousAt.eventually_ne hL,
      (continuousAt_id : ContinuousAt (fun w : ℂ => w) s).eventually_ne hs0] with w hLw hw
    have hrel := χ.LFunction_eq_completed_div_gammaFactor w (.inl hw)
    have hg : χ.gammaFactor w ≠ 0 := by rw [hrel] at hLw; exact (div_ne_zero_iff.mp hLw).2
    apply (eq_div_iff hLw).mpr
    rw [mul_comm]
    exact ((div_eq_iff hg).mp hrel.symm).symm
  rw [(logDeriv_congr_nhds he).eq_of_nhds,logDeriv_div s hCs hL hdC hdL]

lemma primitive_completed_logDeriv_reflection_all (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive)
    (s : ℂ) (hs : -1 < s.re) (hs0 : s.re < 0) :
    logDeriv χ.completedLFunction s+
      logDeriv (χ⁻¹).completedLFunction (1-s)= -log (q : ℂ) := by
  have hpi : (χ⁻¹).IsPrimitive := by
    change (χ⁻¹).conductor=q
    rw [DirichletCharacter.conductor_inv]
    exact hp
  have hright : 1 < (1-s).re := by simp only [sub_re,one_re]; linarith
  have hLs := primitive_LFunction_ne_zero_negative_strip q χ hp s hs hs0
  have hsne : s ≠ 0 := by intro he; simp [he] at hs0
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at hs0
  have hrne : 1-s ≠ 0 := by intro he; rw [he] at hright; norm_num at hright
  have hr1 : 1-s ≠ 1 := by intro he; rw [he] at hright; norm_num at hright
  have hLr := DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ⁻¹) (.inr hr1) hright.le
  have hCs : χ.completedLFunction s ≠ 0 := by
    rw [χ.LFunction_eq_completed_div_gammaFactor s (.inl hsne)] at hLs
    exact (div_ne_zero_iff.mp hLs).1
  have hCr : (χ⁻¹).completedLFunction (1-s) ≠ 0 := by
    rw [(χ⁻¹).LFunction_eq_completed_div_gammaFactor (1-s) (.inl hrne)] at hLr
    exact (div_ne_zero_iff.mp hLr).1
  let P : ℂ → ℂ := fun w => (q : ℂ)^(w-1/2)
  let ε : ℂ := (χ⁻¹).rootNumber
  have hE : (fun w : ℂ => (χ⁻¹).completedLFunction (1-w))=
      (fun w : ℂ => P w*ε*χ.completedLFunction w) := by
    funext w
    simpa only [inv_inv,P,ε] using hpi.completedLFunction_one_sub w
  have hε : ε ≠ 0 := by
    have he := congrFun hE s
    rw [he] at hCr
    exact right_ne_zero_of_mul (left_ne_zero_of_mul hCr)
  have hP : P s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (.inl (by exact_mod_cast NeZero.ne q))
  have hdP : DifferentiableAt ℂ P s :=
    (differentiableAt_id.sub_const (1/2 : ℂ)).const_cpow (.inl (by exact_mod_cast NeZero.ne q))
  have hdC := χ.differentiableAt_completedLFunction s (.inl hsne) (.inl hs1)
  have hdCi := (χ⁻¹).differentiableAt_completedLFunction (1-s) (.inl hrne) (.inl hr1)
  have hlog := congrArg (fun F : ℂ → ℂ => logDeriv F s) hE
  have hcomp : logDeriv (fun w : ℂ => (χ⁻¹).completedLFunction (1-w)) s=
      -logDeriv (χ⁻¹).completedLFunction (1-s) := by
    change logDeriv ((χ⁻¹).completedLFunction ∘ (fun w : ℂ => 1-w)) s = _
    rw [logDeriv_comp hdCi ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id)]
    simp
  have hpLog : logDeriv P s=log (q : ℂ) := by
    rw [logDeriv_apply]
    have hd := Complex.deriv_const_cpow (x := s) (differentiableAt_id.sub_const (1/2 : ℂ)) (q : ℂ)
    have hd' : deriv P s=log (q : ℂ)*P s := by simpa [P] using hd
    rw [hd']
    exact mul_div_cancel_right₀ _ hP
  rw [hcomp,logDeriv_mul (f := fun w : ℂ => P w*ε) (g := χ.completedLFunction)
    s (mul_ne_zero hP hε) hCs (hdP.mul_const ε) hdC,
    logDeriv_mul_const (f := P) s ε hε,hpLog] at hlog
  linear_combination -hlog

theorem primitive_negative_strip_logDeriv_prime_series_all
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive)
    (s : ℂ) (hs : -1 < s.re) (hs0 : s.re < 0) :
    LSeriesSummable (fun n : ℕ => χ⁻¹ n*(ArithmeticFunction.vonMangoldt n : ℂ)) (1-s) ∧
      -deriv χ.LFunction s/χ.LFunction s = log (q : ℂ)+
        deriv χ.gammaFactor s/χ.gammaFactor s+
        deriv (χ⁻¹).gammaFactor (1-s)/(χ⁻¹).gammaFactor (1-s)-
        LSeries (fun n : ℕ => χ⁻¹ n*(ArithmeticFunction.vonMangoldt n : ℂ)) (1-s) := by
  have hr : 1 < (1-s).re := by simp only [sub_re,one_re]; linarith
  have hec : ((fun n : ℕ => χ⁻¹ n)*(fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)))=
      (fun n : ℕ => χ⁻¹ n*(ArithmeticFunction.vonMangoldt n : ℂ)) := by ext n; rfl
  refine ⟨?_,?_⟩
  · simpa only [hec] using (χ⁻¹).LSeriesSummable_twist_vonMangoldt hr
  · have hLs := primitive_LFunction_ne_zero_negative_strip q χ hp s hs hs0
    have hsne : s ≠ 0 := by intro he; simp [he] at hs0
    have hs1 : s ≠ 1 := by intro he; norm_num [he] at hs0
    have hrne : 1-s ≠ 0 := by intro he; rw [he] at hr; norm_num at hr
    have hr1 : 1-s ≠ 1 := by intro he; rw [he] at hr; norm_num at hr
    have hLr := DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ⁻¹) (.inr hr1) hr.le
    have hg := gammaFactor_logDeriv_from_LFunction_local q χ s hsne hs1 hLs
    have hgi := gammaFactor_logDeriv_from_LFunction_local q (χ⁻¹) (1-s) hrne hr1 hLr
    have href := primitive_completed_logDeriv_reflection_all q χ hp s hs hs0
    have hseries := (χ⁻¹).LSeries_twist_vonMangoldt_eq hr
    rw [← (χ⁻¹).deriv_LFunction_eq_deriv_LSeries hr,← (χ⁻¹).LFunction_eq_LSeries hr] at hseries
    simp only [hec] at hseries
    simp only [logDeriv_apply] at hg hgi href
    linear_combination -hg-hgi-href+hseries

end Helfgott
end

-- Original accepted supplier closure, raresbuhai/Helfgott; reused dependency only.
end P2MFinalSource015

/- Source module: CompletedReflectionLocalV1
   Original SHA256: d9410c7282492ddeb161b44b625f0e5c79e228d73e3c918b6b1e792b06a42d79 -/
section P2MFinalSource016

open MeasureTheory Set Filter Complex
open scoped Topology
set_option autoImplicit false

namespace RiemannVonMangoldt

/-- Local extension of the accepted raresbuhai/Helfgott conductor identity.
The proof follows the genuine completed functional equation, retaining both
nonvanishing hypotheses and both possible pole exclusions. Includes q = 1.
This is an internal dependency for contour assembly, not a new public target. -/
theorem primitive_completed_logDeriv_reflection_local (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive)
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hLs : χ.LFunction s ≠ 0) (hLr : (χ⁻¹).LFunction (1-s) ≠ 0) :
    logDeriv χ.completedLFunction s+
      logDeriv (χ⁻¹).completedLFunction (1-s)= -log (q : ℂ) := by
  have hpi : (χ⁻¹).IsPrimitive := by
    change (χ⁻¹).conductor=q
    rw [DirichletCharacter.conductor_inv]
    exact hp
  have hrne : 1-s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hr1 : 1-s ≠ 1 := by
    intro h
    apply hs0
    linear_combination -h
  have hCs : χ.completedLFunction s ≠ 0 := by
    rw [χ.LFunction_eq_completed_div_gammaFactor s (.inl hs0)] at hLs
    exact (div_ne_zero_iff.mp hLs).1
  have hCr : (χ⁻¹).completedLFunction (1-s) ≠ 0 := by
    rw [(χ⁻¹).LFunction_eq_completed_div_gammaFactor (1-s) (.inl hrne)] at hLr
    exact (div_ne_zero_iff.mp hLr).1
  let P : ℂ → ℂ := fun w => (q : ℂ)^(w-1/2)
  let ε : ℂ := (χ⁻¹).rootNumber
  have hE : (fun w : ℂ => (χ⁻¹).completedLFunction (1-w))=
      (fun w : ℂ => P w*ε*χ.completedLFunction w) := by
    funext w
    simpa only [inv_inv,P,ε] using hpi.completedLFunction_one_sub w
  have hε : ε ≠ 0 := by
    have he := congrFun hE s
    rw [he] at hCr
    exact right_ne_zero_of_mul (left_ne_zero_of_mul hCr)
  have hP : P s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (.inl (by exact_mod_cast NeZero.ne q))
  have hdP : DifferentiableAt ℂ P s :=
    (differentiableAt_id.sub_const (1/2 : ℂ)).const_cpow (.inl (by exact_mod_cast NeZero.ne q))
  have hdC := χ.differentiableAt_completedLFunction s (.inl hs0) (.inl hs1)
  have hdCi := (χ⁻¹).differentiableAt_completedLFunction (1-s) (.inl hrne) (.inl hr1)
  have hlog := congrArg (fun F : ℂ → ℂ => logDeriv F s) hE
  have hcomp : logDeriv (fun w : ℂ => (χ⁻¹).completedLFunction (1-w)) s=
      -logDeriv (χ⁻¹).completedLFunction (1-s) := by
    change logDeriv ((χ⁻¹).completedLFunction ∘ (fun w : ℂ => 1-w)) s = _
    rw [logDeriv_comp hdCi ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id)]
    simp
  have hpLog : logDeriv P s=log (q : ℂ) := by
    rw [logDeriv_apply]
    have hd := Complex.deriv_const_cpow (x := s) (differentiableAt_id.sub_const (1/2 : ℂ)) (q : ℂ)
    have hd' : deriv P s=log (q : ℂ)*P s := by simpa [P] using hd
    rw [hd']
    exact mul_div_cancel_right₀ _ hP
  rw [hcomp,logDeriv_mul (f := fun w : ℂ => P w*ε) (g := χ.completedLFunction)
    s (mul_ne_zero hP hε) hCs (hdP.mul_const ε) hdC,
    logDeriv_mul_const (f := P) s ε hε,hpLog] at hlog
  linear_combination -hlog

/-- The original L-function reflection identity at regular nonzero points. -/
theorem primitive_LFunction_logDeriv_reflection_local (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive)
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hLs : χ.LFunction s ≠ 0) (hLr : (χ⁻¹).LFunction (1-s) ≠ 0) :
    logDeriv χ.LFunction s + logDeriv (χ⁻¹).LFunction (1-s) =
      -log (q : ℂ) - logDeriv χ.gammaFactor s -
        logDeriv (χ⁻¹).gammaFactor (1-s) := by
  have hrne : 1-s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hr1 : 1-s ≠ 1 := by
    intro h
    apply hs0
    linear_combination -h
  have hg := Helfgott.gammaFactor_logDeriv_from_LFunction_local q χ s hs0 hs1 hLs
  have hgi := Helfgott.gammaFactor_logDeriv_from_LFunction_local q (χ⁻¹) (1-s) hrne hr1 hLr
  have href := primitive_completed_logDeriv_reflection_local q χ hp s hs0 hs1 hLs hLr
  linear_combination hg + hgi + href

end RiemannVonMangoldt
end P2MFinalSource016

/- Source module: CompletedReflectionNonzeroV1
   Original SHA256: ea59482198f42e3c5acbfb0e68abf58cc72067ef105ce91b58471aa81eda5477 -/
section P2MFinalSource017

/-!
Reuse the checked local functional-equation proof with its actual completed
nonvanishing hypotheses. This removes only the preliminary conversion from
original-L nonvanishing; pole exclusions and all derivative identities remain.
-/

open MeasureTheory Set Filter Complex
open scoped Topology
set_option autoImplicit false

namespace RiemannVonMangoldt

theorem primitive_completed_logDeriv_reflection_of_completed_ne_zero (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive)
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hCs : χ.completedLFunction s ≠ 0)
    (hCr : (χ⁻¹).completedLFunction (1-s) ≠ 0) :
    logDeriv χ.completedLFunction s+
      logDeriv (χ⁻¹).completedLFunction (1-s)= -log (q : ℂ) := by
  have hpi : (χ⁻¹).IsPrimitive := by
    change (χ⁻¹).conductor=q
    rw [DirichletCharacter.conductor_inv]
    exact hp
  have hrne : 1-s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hr1 : 1-s ≠ 1 := by
    intro h
    apply hs0
    linear_combination -h
  let P : ℂ → ℂ := fun w => (q : ℂ)^(w-1/2)
  let ε : ℂ := (χ⁻¹).rootNumber
  have hE : (fun w : ℂ => (χ⁻¹).completedLFunction (1-w))=
      (fun w : ℂ => P w*ε*χ.completedLFunction w) := by
    funext w
    simpa only [inv_inv,P,ε] using hpi.completedLFunction_one_sub w
  have hε : ε ≠ 0 := by
    have he := congrFun hE s
    rw [he] at hCr
    exact right_ne_zero_of_mul (left_ne_zero_of_mul hCr)
  have hP : P s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (.inl (by exact_mod_cast NeZero.ne q))
  have hdP : DifferentiableAt ℂ P s :=
    (differentiableAt_id.sub_const (1/2 : ℂ)).const_cpow (.inl (by exact_mod_cast NeZero.ne q))
  have hdC := χ.differentiableAt_completedLFunction s (.inl hs0) (.inl hs1)
  have hdCi := (χ⁻¹).differentiableAt_completedLFunction (1-s) (.inl hrne) (.inl hr1)
  have hlog := congrArg (fun F : ℂ → ℂ => logDeriv F s) hE
  have hcomp : logDeriv (fun w : ℂ => (χ⁻¹).completedLFunction (1-w)) s=
      -logDeriv (χ⁻¹).completedLFunction (1-s) := by
    change logDeriv ((χ⁻¹).completedLFunction ∘ (fun w : ℂ => 1-w)) s = _
    rw [logDeriv_comp hdCi ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id)]
    simp
  have hpLog : logDeriv P s=log (q : ℂ) := by
    rw [logDeriv_apply]
    have hd := Complex.deriv_const_cpow (x := s) (differentiableAt_id.sub_const (1/2 : ℂ)) (q : ℂ)
    have hd' : deriv P s=log (q : ℂ)*P s := by simpa [P] using hd
    rw [hd']
    exact mul_div_cancel_right₀ _ hP
  rw [hcomp,logDeriv_mul (f := fun w : ℂ => P w*ε) (g := χ.completedLFunction)
    s (mul_ne_zero hP hε) hCs (hdP.mul_const ε) hdC,
    logDeriv_mul_const (f := P) s ε hε,hpLog] at hlog
  linear_combination -hlog

end RiemannVonMangoldt

end P2MFinalSource017

/- Source module: DirichletContourReflectionV3
   Original SHA256: 2cd7e780b71d23004e712a1eaad2b6a5fc7a8ea97bd6b9dc87c582f0b9089449 -/
section P2MFinalSource018

/-!
Exact four-edge reflection algebra on the original counting rectangle.
The character and inverse character remain distinct. All substitutions are
actual interval-integral substitutions, with the required integrability
proved from genuine completed-function boundary nonvanishing.
-/

set_option autoImplicit false

open Complex Set MeasureTheory
open scoped Interval Topology

namespace RiemannVonMangoldt.Contour

open RectKernel CountBridge

abbrev rectangleBoundary (T : ℝ) : Set ℂ :=
  (Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-T) T) \
    (Ioo (-1 / 2 : ℝ) (3 / 2) ×ℂ Ioo (-T) T)

noncomputable def horizontal (f : ℂ → ℂ) (t : ℝ) : ℂ :=
  ∫ x : ℝ in (1 / 2)..(3 / 2), f ((x : ℂ) + (t : ℂ) * I)

noncomputable def rightVertical (f : ℂ → ℂ) (T : ℝ) : ℂ :=
  ∫ y : ℝ in (-T)..T, f (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)

lemma bottom_mem_boundary {T x : ℝ} (hT : 0 < T)
    (hx : x ∈ Icc (-1 / 2 : ℝ) (3 / 2)) :
    (x : ℂ) + ((-T : ℝ) : ℂ) * I ∈ rectangleBoundary T := by
  refine ⟨?_, ?_⟩
  · change
      (((x : ℂ) + ((-T : ℝ) : ℂ) * I).re ∈ Icc (-1 / 2 : ℝ) (3 / 2)) ∧
      (((x : ℂ) + ((-T : ℝ) : ℂ) * I).im ∈ Icc (-T) T)
    simpa using And.intro hx (show -T ∈ Icc (-T) T from ⟨le_rfl, by linarith⟩)
  · intro hz
    have hh : -T < -T := by simpa using hz.2.1
    exact (lt_irrefl (-T)) hh

lemma top_mem_boundary {T x : ℝ} (hT : 0 < T)
    (hx : x ∈ Icc (-1 / 2 : ℝ) (3 / 2)) :
    (x : ℂ) + (T : ℂ) * I ∈ rectangleBoundary T := by
  refine ⟨?_, ?_⟩
  · change
      (((x : ℂ) + (T : ℂ) * I).re ∈ Icc (-1 / 2 : ℝ) (3 / 2)) ∧
      (((x : ℂ) + (T : ℂ) * I).im ∈ Icc (-T) T)
    simpa using And.intro hx (show T ∈ Icc (-T) T from ⟨by linarith, le_rfl⟩)
  · intro hz
    have hh : T < T := by simpa using hz.2.2
    exact (lt_irrefl T) hh

lemma right_mem_boundary {T y : ℝ} (hy : y ∈ Icc (-T) T) :
    ((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I ∈ rectangleBoundary T := by
  refine ⟨?_, ?_⟩
  · change
      ((((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I).re ∈ Icc (-1 / 2 : ℝ) (3 / 2)) ∧
      ((((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I).im ∈ Icc (-T) T)
    simpa using And.intro (show (3 / 2 : ℝ) ∈ Icc (-1 / 2 : ℝ) (3 / 2)
      from ⟨by norm_num, le_rfl⟩) hy
  · intro hz
    have hh : (3 / 2 : ℝ) < 3 / 2 := by simpa using hz.1.2
    exact (lt_irrefl (3 / 2 : ℝ)) hh

lemma left_mem_boundary {T y : ℝ} (hy : y ∈ Icc (-T) T) :
    ((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I ∈ rectangleBoundary T := by
  refine ⟨?_, ?_⟩
  · change
      ((((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I).re ∈ Icc (-1 / 2 : ℝ) (3 / 2)) ∧
      ((((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I).im ∈ Icc (-T) T)
    simpa using And.intro (show (-1 / 2 : ℝ) ∈ Icc (-1 / 2 : ℝ) (3 / 2)
      from ⟨le_rfl, by norm_num⟩) hy
  · intro hz
    have hh : (-1 / 2 : ℝ) < -1 / 2 := by simpa using hz.1.1
    exact (lt_irrefl (-1 / 2 : ℝ)) hh

lemma one_sub_mem_boundary {T : ℝ} {z : ℂ} (hz : z ∈ rectangleBoundary T) :
    1 - z ∈ rectangleBoundary T := by
  refine ⟨?_, ?_⟩
  · change
      ((-1 / 2 : ℝ) ≤ (1 - z).re ∧ (1 - z).re ≤ 3 / 2) ∧
      -T ≤ (1 - z).im ∧ (1 - z).im ≤ T
    simp only [sub_re, one_re, sub_im, one_im, zero_sub]
    exact ⟨⟨by linarith [hz.1.1.2], by linarith [hz.1.1.1]⟩,
      ⟨by linarith [hz.1.2.2], by linarith [hz.1.2.1]⟩⟩
  · rintro ⟨⟨hl, hr⟩, ⟨hb, ht⟩⟩
    apply hz.2
    simp only [sub_re, one_re, sub_im, one_im, zero_sub] at hl hr hb ht
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem completedLogDeriv_boundaryIntegrable
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (T : ℝ) (hT : 0 < T)
    (hB : ∀ z ∈ rectangleBoundary T, chi.completedLFunction z ≠ 0) :
    BoundaryIntegrable (-1 / 2) (3 / 2) (-T) T (logDeriv chi.completedLFunction) := by
  have hc : ContinuousOn (logDeriv chi.completedLFunction) (rectangleBoundary T) := by
    intro z hz
    obtain ⟨hz0, hz1⟩ := rectangle_boundary_ne_zero_ne_one hT hz
    have ha := analyticAt_completedLFunction_of_ne chi hz0 hz1
    exact (ha.deriv.div ha (hB z hz)).continuousAt.continuousWithinAt
  have hab : (-1 / 2 : ℝ) ≤ 3 / 2 := by norm_num
  have hcd : -T ≤ T := by linarith
  have hb : MapsTo (fun x : ℝ => (x : ℂ) + ((-T : ℝ) : ℂ) * I)
      (uIcc (-1 / 2) (3 / 2)) (rectangleBoundary T) := by
    intro x hx
    exact bottom_mem_boundary hT (by simpa only [uIcc_of_le hab] using hx)
  have ht : MapsTo (fun x : ℝ => (x : ℂ) + (T : ℂ) * I)
      (uIcc (-1 / 2) (3 / 2)) (rectangleBoundary T) := by
    intro x hx
    exact top_mem_boundary hT (by simpa only [uIcc_of_le hab] using hx)
  have hr : MapsTo (fun y : ℝ => ((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)
      (uIcc (-T) T) (rectangleBoundary T) := by
    intro y hy
    exact right_mem_boundary (by simpa only [uIcc_of_le hcd] using hy)
  have hl : MapsTo (fun y : ℝ => ((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)
      (uIcc (-T) T) (rectangleBoundary T) := by
    intro y hy
    exact left_mem_boundary (by simpa only [uIcc_of_le hcd] using hy)
  exact ⟨(hc.comp (by fun_prop) hb).intervalIntegrable,
    (hc.comp (by fun_prop) ht).intervalIntegrable,
    (hc.comp (by fun_prop) hr).intervalIntegrable,
    (hc.comp (by fun_prop) hl).intervalIntegrable⟩

lemma horizontal_integrable_of_full (f : ℂ → ℂ) (t : ℝ)
    (hf : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (t : ℂ) * I))
      volume (-1 / 2) (3 / 2)) :
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (t : ℂ) * I))
      volume (1 / 2) (3 / 2) := by
  apply hf.mono_set
  intro x hx
  rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2)] at hx
  rw [uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 3 / 2)]
  exact ⟨by linarith [hx.1], hx.2⟩

private lemma full_horizontal_of_reflection
    (f g : ℂ → ℂ) (c : ℂ) (t : ℝ)
    (hf : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (t : ℂ) * I))
      volume (-1 / 2) (3 / 2))
    (hg : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + ((-t : ℝ) : ℂ) * I))
      volume (1 / 2) (3 / 2))
    (hEq : ∀ x ∈ Icc (-1 / 2 : ℝ) (1 / 2),
      f ((x : ℂ) + (t : ℂ) * I) +
        g (((1 - x : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) = -c) :
    (∫ x : ℝ in (-1 / 2)..(3 / 2), f ((x : ℂ) + (t : ℂ) * I)) =
      -c - horizontal g (-t) + horizontal f t := by
  have hfl : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (t : ℂ) * I))
      volume (-1 / 2) (1 / 2) := by
    apply hf.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] at hx
    rw [uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 3 / 2)]
    exact ⟨hx.1, by linarith [hx.2]⟩
  have hfr := horizontal_integrable_of_full f t hf
  have hgr : IntervalIntegrable
      (fun x : ℝ => g (((1 - x : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I))
      volume (-1 / 2) (1 / 2) := by
    convert (hg.comp_sub_left 1).symm using 1 <;> norm_num
  have hleft :
      (∫ x : ℝ in (-1 / 2)..(1 / 2), f ((x : ℂ) + (t : ℂ) * I)) =
      ∫ x : ℝ in (-1 / 2)..(1 / 2),
        -c - g (((1 - x : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
      simpa only [uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] using hx
    linear_combination hEq x hx'
  have hcint : (∫ _x : ℝ in (-1 / 2)..(1 / 2), -c) = -c := by
    rw [intervalIntegral.integral_const]
    norm_num
  have hgint :
      (∫ x : ℝ in (-1 / 2)..(1 / 2),
        g (((1 - x : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)) = horizontal g (-t) := by
    have h := intervalIntegral.integral_comp_sub_left
      (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
      (fun u : ℝ => g ((u : ℂ) + ((-t : ℝ) : ℂ) * I)) (1 : ℝ)
    simpa only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
      show (1 : ℝ) - (-1 / 2) = 3 / 2 by norm_num, horizontal] using h
  rw [← intervalIntegral.integral_add_adjacent_intervals hfl hfr, hleft,
    intervalIntegral.integral_sub intervalIntegrable_const hgr, hcint, hgint]
  rfl

private lemma left_vertical_of_reflection
    (f g : ℂ → ℂ) (c : ℂ) (T : ℝ) (hT : 0 < T)
    (hg : IntervalIntegrable
      (fun y : ℝ => g (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) volume (-T) T)
    (hEq : ∀ y ∈ Icc (-T) T,
      f (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) +
        g (((3 / 2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) = -c) :
    (∫ y : ℝ in (-T)..T, f (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) =
      -(2 * (T : ℂ) * c) - rightVertical g T := by
  have hgr : IntervalIntegrable
      (fun y : ℝ => g (((3 / 2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I)) volume (-T) T := by
    simpa only [zero_sub, sub_neg_eq_add, zero_add, neg_neg] using (hg.comp_sub_left 0).symm
  have he :
      (∫ y : ℝ in (-T)..T, f (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) =
      ∫ y : ℝ in (-T)..T,
        -c - g (((3 / 2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hy' : y ∈ Icc (-T) T := by
      simpa only [uIcc_of_le (show -T ≤ T by linarith)] using hy
    linear_combination hEq y hy'
  have hcint : (∫ _y : ℝ in (-T)..T, -c) = -(2 * (T : ℂ) * c) := by
    rw [intervalIntegral.integral_const]
    simp only [Complex.real_smul, ofReal_sub, ofReal_neg]
    ring
  have hgint :
      (∫ y : ℝ in (-T)..T,
        g (((3 / 2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I)) = rightVertical g T := by
    simpa only [neg_neg, rightVertical] using
      intervalIntegral.integral_comp_neg
        (fun y : ℝ => g (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) (a := -T) (b := T)
  rw [he, intervalIntegral.integral_sub intervalIntegrable_const hgr, hcint, hgint]

/-- The completed boundary is the two right edges, the four signed right
half-horizontal terms, and the actual conductor term. This identity does
not identify the character with its inverse or use zero-count symmetry. -/
theorem primitive_completed_boundary_paired
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hp : chi.IsPrimitive)
    (T : ℝ) (hT : 0 < T)
    (hB : ∀ z ∈ rectangleBoundary T, chi.completedLFunction z ≠ 0)
    (hiB : ∀ z ∈ rectangleBoundary T, (chi⁻¹).completedLFunction z ≠ 0) :
    boundary (-1 / 2) (3 / 2) (-T) T (logDeriv chi.completedLFunction) =
      2 * I * (T : ℂ) * log (q : ℂ) +
      I * (rightVertical (logDeriv chi.completedLFunction) T +
        rightVertical (logDeriv (chi⁻¹).completedLFunction) T) +
      horizontal (logDeriv chi.completedLFunction) (-T) +
      horizontal (logDeriv (chi⁻¹).completedLFunction) (-T) -
      horizontal (logDeriv chi.completedLFunction) T -
      horizontal (logDeriv (chi⁻¹).completedLFunction) T := by
  have hI := completedLogDeriv_boundaryIntegrable chi T hT hB
  have hiI := completedLogDeriv_boundaryIntegrable (chi⁻¹) T hT hiB
  have href (z : ℂ) (hz : z ∈ rectangleBoundary T) :
      logDeriv chi.completedLFunction z + logDeriv (chi⁻¹).completedLFunction (1 - z) =
        -log (q : ℂ) := by
    obtain ⟨hz0, hz1⟩ := rectangle_boundary_ne_zero_ne_one hT hz
    exact primitive_completed_logDeriv_reflection_of_completed_ne_zero q chi hp z hz0 hz1
      (hB z hz) (hiB (1 - z) (one_sub_mem_boundary hz))
  have hbottom :
      (∫ x : ℝ in (-1 / 2)..(3 / 2),
        logDeriv chi.completedLFunction ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) =
      -log (q : ℂ) - horizontal (logDeriv (chi⁻¹).completedLFunction) T +
        horizontal (logDeriv chi.completedLFunction) (-T) := by
    have hg := horizontal_integrable_of_full (logDeriv (chi⁻¹).completedLFunction) T hiI.2.1
    have hEq : ∀ x ∈ Icc (-1 / 2 : ℝ) (1 / 2),
        logDeriv chi.completedLFunction ((x : ℂ) + ((-T : ℝ) : ℂ) * I) +
          logDeriv (chi⁻¹).completedLFunction
            (((1 - x : ℝ) : ℂ) + ((-(-T) : ℝ) : ℂ) * I) = -log (q : ℂ) := by
      intro x hx
      have hz := bottom_mem_boundary hT (show x ∈ Icc (-1 / 2 : ℝ) (3 / 2)
        from ⟨hx.1, by linarith [hx.2]⟩)
      have he : 1 - ((x : ℂ) + ((-T : ℝ) : ℂ) * I) =
          ((1 - x : ℝ) : ℂ) + ((-(-T) : ℝ) : ℂ) * I := by push_cast; ring
      simpa only [he] using href _ hz
    simpa only [neg_neg] using full_horizontal_of_reflection
      (logDeriv chi.completedLFunction) (logDeriv (chi⁻¹).completedLFunction)
      (log (q : ℂ)) (-T) hI.1 (by simpa only [neg_neg] using hg) hEq
  have htop :
      (∫ x : ℝ in (-1 / 2)..(3 / 2),
        logDeriv chi.completedLFunction ((x : ℂ) + (T : ℂ) * I)) =
      -log (q : ℂ) - horizontal (logDeriv (chi⁻¹).completedLFunction) (-T) +
        horizontal (logDeriv chi.completedLFunction) T := by
    apply full_horizontal_of_reflection (logDeriv chi.completedLFunction)
      (logDeriv (chi⁻¹).completedLFunction) (log (q : ℂ)) T hI.2.1
      (horizontal_integrable_of_full (logDeriv (chi⁻¹).completedLFunction) (-T) hiI.1)
    intro x hx
    have hz := top_mem_boundary hT (show x ∈ Icc (-1 / 2 : ℝ) (3 / 2)
      from ⟨hx.1, by linarith [hx.2]⟩)
    have he : 1 - ((x : ℂ) + (T : ℂ) * I) =
        ((1 - x : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I := by push_cast; ring
    simpa only [he] using href _ hz
  have hleft :
      (∫ y : ℝ in (-T)..T,
        logDeriv chi.completedLFunction (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) =
      -(2 * (T : ℂ) * log (q : ℂ)) -
        rightVertical (logDeriv (chi⁻¹).completedLFunction) T := by
    apply left_vertical_of_reflection (logDeriv chi.completedLFunction)
      (logDeriv (chi⁻¹).completedLFunction) (log (q : ℂ)) T hT hiI.2.2.1
    intro y hy
    have he : 1 - (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) =
        ((3 / 2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I := by push_cast; ring
    simpa only [he] using href _ (left_mem_boundary hy)
  unfold boundary
  rw [hbottom, htop, hleft]
  change _ - _ + I * rightVertical (logDeriv chi.completedLFunction) T - I * _ = _
  ring

end RiemannVonMangoldt.Contour

end P2MFinalSource018

/- Source module: DirichletContourSplitV3
   Original SHA256: 82becc06fbe11204095343c5f39e1cfbb5e3222fb01f522f291a87c3fc988225 -/
section P2MFinalSource019

/-!
Split the exact paired completed contour identity into original-L and gamma
integrals. Every split uses the genuine local completion identity, with
explicit pointwise nonvanishing and actual interval integrability.
-/

set_option autoImplicit false

open Complex Set Filter MeasureTheory
open scoped Interval Topology

namespace RiemannVonMangoldt.Contour

open RectKernel CountBridge

lemma analyticAt_LFunction_of_ne_one {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ chi.LFunction s := by
  apply analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [eventually_ne_nhds hs] with w hw
  exact chi.differentiableAt_LFunction w (.inl hw)

theorem horizontal_completed_split
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (t : ℝ) (ht : t ≠ 0)
    (hL : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2),
      chi.LFunction ((x : ℂ) + (t : ℂ) * I) ≠ 0)
    (hC : IntervalIntegrable
      (fun x : ℝ => logDeriv chi.completedLFunction ((x : ℂ) + (t : ℂ) * I))
      volume (1 / 2) (3 / 2)) :
    IntervalIntegrable
        (fun x : ℝ => logDeriv chi.LFunction ((x : ℂ) + (t : ℂ) * I))
        volume (1 / 2) (3 / 2) ∧
      IntervalIntegrable
        (fun x : ℝ => logDeriv chi.gammaFactor ((x : ℂ) + (t : ℂ) * I))
        volume (1 / 2) (3 / 2) ∧
      horizontal (logDeriv chi.completedLFunction) t =
        horizontal (logDeriv chi.LFunction) t + horizontal (logDeriv chi.gammaFactor) t := by
  have hs0 (x : ℝ) : (x : ℂ) + (t : ℂ) * I ≠ 0 := by
    intro he
    exact ht (by simpa using congrArg Complex.im he)
  have hs1 (x : ℝ) : (x : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro he
    exact ht (by simpa using congrArg Complex.im he)
  have hLI : IntervalIntegrable
      (fun x : ℝ => logDeriv chi.LFunction ((x : ℂ) + (t : ℂ) * I))
      volume (1 / 2) (3 / 2) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx' : x ∈ Icc (1 / 2 : ℝ) (3 / 2) := by
      simpa only [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2)] using hx
    have ha := analyticAt_LFunction_of_ne_one chi (hs1 x)
    have hlog : ContinuousAt (logDeriv chi.LFunction) ((x : ℂ) + (t : ℂ) * I) :=
      (ha.deriv.div ha (hL x hx')).continuousAt
    have hpath : ContinuousAt (fun u : ℝ => (u : ℂ) + (t : ℂ) * I) x := by fun_prop
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun u : ℝ => (u : ℂ) + (t : ℂ) * I) (g := logDeriv chi.LFunction)
      hlog hpath.continuousWithinAt
  have hEq : EqOn
      (fun x : ℝ => logDeriv chi.completedLFunction ((x : ℂ) + (t : ℂ) * I) -
        logDeriv chi.LFunction ((x : ℂ) + (t : ℂ) * I))
      (fun x : ℝ => logDeriv chi.gammaFactor ((x : ℂ) + (t : ℂ) * I))
      (uIcc (1 / 2) (3 / 2)) := by
    intro x hx
    have hx' : x ∈ Icc (1 / 2 : ℝ) (3 / 2) := by
      simpa only [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2)] using hx
    exact (Helfgott.gammaFactor_logDeriv_from_LFunction_local q chi
      ((x : ℂ) + (t : ℂ) * I) (hs0 x) (hs1 x) (hL x hx')).symm
  have hGI : IntervalIntegrable
      (fun x : ℝ => logDeriv chi.gammaFactor ((x : ℂ) + (t : ℂ) * I))
      volume (1 / 2) (3 / 2) :=
    (intervalIntegrable_congr (fun x hx => hEq (uIoc_subset_uIcc hx))).mp (hC.sub hLI)
  have hGint : horizontal (logDeriv chi.gammaFactor) t =
      horizontal (logDeriv chi.completedLFunction) t - horizontal (logDeriv chi.LFunction) t := by
    exact (intervalIntegral.integral_congr hEq).symm.trans
      (intervalIntegral.integral_sub hC hLI)
  refine ⟨hLI, hGI, ?_⟩
  linear_combination -hGint

theorem rightVertical_completed_split
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (T : ℝ)
    (hC : IntervalIntegrable
      (fun y : ℝ => logDeriv chi.completedLFunction (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))
      volume (-T) T) :
    IntervalIntegrable
        (fun y : ℝ => logDeriv chi.LFunction (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))
        volume (-T) T ∧
      IntervalIntegrable
        (fun y : ℝ => logDeriv chi.gammaFactor (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))
        volume (-T) T ∧
      rightVertical (logDeriv chi.completedLFunction) T =
        rightVertical (logDeriv chi.LFunction) T + rightVertical (logDeriv chi.gammaFactor) T := by
  have hs0 (y : ℝ) : ((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    norm_num at hh
  have hs1 (y : ℝ) : ((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I ≠ 1 := by
    intro he
    have hh := congrArg Complex.re he
    norm_num at hh
  have hL (y : ℝ) : chi.LFunction (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 :=
    chi.LFunction_ne_zero_of_one_le_re (.inr (hs1 y)) (by norm_num)
  have hLI : IntervalIntegrable
      (fun y : ℝ => logDeriv chi.LFunction (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))
      volume (-T) T := by
    apply ContinuousOn.intervalIntegrable
    intro y _
    have ha := analyticAt_LFunction_of_ne_one chi (hs1 y)
    have hlog : ContinuousAt (logDeriv chi.LFunction)
        (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) :=
      (ha.deriv.div ha (hL y)).continuousAt
    have hpath : ContinuousAt
        (fun u : ℝ => ((3 / 2 : ℝ) : ℂ) + (u : ℂ) * I) y := by fun_prop
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun u : ℝ => ((3 / 2 : ℝ) : ℂ) + (u : ℂ) * I)
      (g := logDeriv chi.LFunction) hlog hpath.continuousWithinAt
  have hEq : EqOn
      (fun y : ℝ => logDeriv chi.completedLFunction (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) -
        logDeriv chi.LFunction (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))
      (fun y : ℝ => logDeriv chi.gammaFactor (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))
      (uIcc (-T) T) := by
    intro y _
    exact (Helfgott.gammaFactor_logDeriv_from_LFunction_local q chi
      (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) (hs0 y) (hs1 y) (hL y)).symm
  have hGI : IntervalIntegrable
      (fun y : ℝ => logDeriv chi.gammaFactor (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))
      volume (-T) T :=
    (intervalIntegrable_congr (fun y hy => hEq (uIoc_subset_uIcc hy))).mp (hC.sub hLI)
  have hGint : rightVertical (logDeriv chi.gammaFactor) T =
      rightVertical (logDeriv chi.completedLFunction) T - rightVertical (logDeriv chi.LFunction) T := by
    exact (intervalIntegral.integral_congr hEq).symm.trans
      (intervalIntegral.integral_sub hC hLI)
  refine ⟨hLI, hGI, ?_⟩
  linear_combination -hGint

/-- Exact paired contour decomposition into the two original-L vertical
terms, four original-L horizontal terms, their gamma counterparts, and
the actual conductor term. -/
theorem primitive_completed_boundary_L_gamma
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hp : chi.IsPrimitive)
    (T : ℝ) (hT : 0 < T)
    (hchipos : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2),
      chi.LFunction ((x : ℂ) + (T : ℂ) * I) ≠ 0)
    (hchineg : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2),
      chi.LFunction ((x : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0)
    (hipos : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2),
      (chi⁻¹).LFunction ((x : ℂ) + (T : ℂ) * I) ≠ 0)
    (hineg : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2),
      (chi⁻¹).LFunction ((x : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0) :
    boundary (-1 / 2) (3 / 2) (-T) T (logDeriv chi.completedLFunction) =
      2 * I * (T : ℂ) * log (q : ℂ) +
      I * (rightVertical (logDeriv chi.LFunction) T +
        rightVertical (logDeriv (chi⁻¹).LFunction) T) +
      (horizontal (logDeriv chi.LFunction) (-T) +
        horizontal (logDeriv (chi⁻¹).LFunction) (-T) -
        horizontal (logDeriv chi.LFunction) T - horizontal (logDeriv (chi⁻¹).LFunction) T) +
      I * (rightVertical (logDeriv chi.gammaFactor) T +
        rightVertical (logDeriv (chi⁻¹).gammaFactor) T) +
      (horizontal (logDeriv chi.gammaFactor) (-T) +
        horizontal (logDeriv (chi⁻¹).gammaFactor) (-T) -
        horizontal (logDeriv chi.gammaFactor) T - horizontal (logDeriv (chi⁻¹).gammaFactor) T) := by
  have hpi : (chi⁻¹).IsPrimitive := by
    change (chi⁻¹).conductor = q
    rw [DirichletCharacter.conductor_inv]
    exact hp
  have hB := primitive_completedLFunction_boundary_of_paired_good_heights chi hp T
    hchipos hchineg hipos hineg
  have hiB := primitive_completedLFunction_boundary_of_paired_good_heights (chi⁻¹) hpi T
    hipos hineg (by simpa only [inv_inv] using hchipos) (by simpa only [inv_inv] using hchineg)
  have hI := completedLogDeriv_boundaryIntegrable chi T hT hB
  have hiI := completedLogDeriv_boundaryIntegrable (chi⁻¹) T hT hiB
  obtain ⟨_, _, hpos⟩ := horizontal_completed_split chi T hT.ne' hchipos
    (horizontal_integrable_of_full _ T hI.2.1)
  obtain ⟨_, _, hneg⟩ := horizontal_completed_split chi (-T) (neg_ne_zero.mpr hT.ne') hchineg
    (horizontal_integrable_of_full _ (-T) hI.1)
  obtain ⟨_, _, hiposEq⟩ := horizontal_completed_split (chi⁻¹) T hT.ne' hipos
    (horizontal_integrable_of_full _ T hiI.2.1)
  obtain ⟨_, _, hinegEq⟩ := horizontal_completed_split (chi⁻¹) (-T) (neg_ne_zero.mpr hT.ne') hineg
    (horizontal_integrable_of_full _ (-T) hiI.1)
  obtain ⟨_, _, hv⟩ := rightVertical_completed_split chi T hI.2.2.1
  obtain ⟨_, _, hiv⟩ := rightVertical_completed_split (chi⁻¹) T hiI.2.2.1
  rw [primitive_completed_boundary_paired chi hp T hT hB hiB,
    hpos, hneg, hiposEq, hinegEq, hv, hiv]
  ring

/-- Imaginary part of the exact decomposition, in the form needed to bound
the original count error. The conductor contribution is `2*T*log q`.
The inverse character remains explicit in every term. -/
theorem primitive_completed_boundary_im_L_gamma
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hp : chi.IsPrimitive)
    (T : ℝ) (hT : 0 < T)
    (hchipos : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2),
      chi.LFunction ((x : ℂ) + (T : ℂ) * I) ≠ 0)
    (hchineg : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2),
      chi.LFunction ((x : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0)
    (hipos : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2),
      (chi⁻¹).LFunction ((x : ℂ) + (T : ℂ) * I) ≠ 0)
    (hineg : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2),
      (chi⁻¹).LFunction ((x : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0) :
    (boundary (-1 / 2) (3 / 2) (-T) T (logDeriv chi.completedLFunction)).im =
      2 * T * Real.log (q : ℝ) +
      ((rightVertical (logDeriv chi.LFunction) T).re +
        (rightVertical (logDeriv (chi⁻¹).LFunction) T).re) +
      ((horizontal (logDeriv chi.LFunction) (-T)).im +
        (horizontal (logDeriv (chi⁻¹).LFunction) (-T)).im -
        (horizontal (logDeriv chi.LFunction) T).im -
        (horizontal (logDeriv (chi⁻¹).LFunction) T).im) +
      ((rightVertical (logDeriv chi.gammaFactor) T).re +
        (rightVertical (logDeriv (chi⁻¹).gammaFactor) T).re) +
      ((horizontal (logDeriv chi.gammaFactor) (-T)).im +
        (horizontal (logDeriv (chi⁻¹).gammaFactor) (-T)).im -
        (horizontal (logDeriv chi.gammaFactor) T).im -
        (horizontal (logDeriv (chi⁻¹).gammaFactor) T).im) := by
  have he := congrArg Complex.im
    (primitive_completed_boundary_L_gamma chi hp T hT hchipos hchineg hipos hineg)
  simpa [mul_im, mul_re, log_re, Complex.norm_natCast] using he

end RiemannVonMangoldt.Contour

end P2MFinalSource019

/- Source module: NonprincipalPartialSumV3
   Original SHA256: 1d283d8bc1f4193a83d25207e5d3d0f73ffef8d14dd4f6c4b3f5e53022afef65 -/
section P2MFinalSource020

open Finset
set_option autoImplicit false

namespace RiemannVonMangoldt

/-- Finite periodic cancellation bound for the original nonprincipal character.
No absolute convergence of its Dirichlet series in the critical strip is assumed. -/
theorem dirichlet_nonprincipal_partial_sum_norm_le_level
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ range n, χ (((k + 1 : ℕ)) : ZMod q)‖ ≤ (q : ℝ) := by
  classical
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hfin (i : Fin q) : ((i.val : ℕ) : ZMod q) = ZMod.finEquiv q i := by
    cases q with
    | zero => exact Fin.elim0 i
    | succ q =>
      apply ZMod.val_injective (q + 1)
      rw [ZMod.val_natCast_of_lt i.isLt]
      rfl
  have hblock : (∑ k ∈ range q, χ (((k + 1 : ℕ)) : ZMod q)) = 0 := by
    calc
      _ = ∑ i : Fin q, χ (((i.val + 1 : ℕ)) : ZMod q) := by
        exact (Fin.sum_univ_eq_sum_range (fun k : ℕ => χ (((k + 1 : ℕ)) : ZMod q)) q).symm
      _ = ∑ i : Fin q, χ (ZMod.finEquiv q i + 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Nat.cast_add, Nat.cast_one, hfin]
      _ = ∑ a : ZMod q, χ (a + 1) :=
        Equiv.sum_comp (ZMod.finEquiv q).toEquiv (fun a => χ (a + 1))
      _ = ∑ a : ZMod q, χ a :=
        Equiv.sum_comp (Equiv.addRight (1 : ZMod q)) (fun a => χ a)
      _ = 0 := χ.sum_eq_zero_of_ne_one hχ
  have hperiod (k : ℕ) :
      χ (((q + k + 1 : ℕ)) : ZMod q) = χ (((k + 1 : ℕ)) : ZMod q) := by
    simp [Nat.cast_add, ZMod.natCast_self]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < q
    · calc
        _ ≤ ∑ k ∈ range n, ‖χ (((k + 1 : ℕ)) : ZMod q)‖ := norm_sum_le _ _
        _ ≤ ∑ _k ∈ range n, (1 : ℝ) :=
          Finset.sum_le_sum (fun k _ => χ.norm_le_one _)
        _ = (n : ℝ) := by simp
        _ ≤ (q : ℝ) := by exact_mod_cast hn.le
    · have heq : n = q + (n - q) := by omega
      have hlt : n - q < n := by omega
      conv_lhs => rw [heq, Finset.sum_range_add, hblock, zero_add]
      simp_rw [hperiod]
      exact ih (n - q) hlt

end RiemannVonMangoldt

end P2MFinalSource020

/- Source module: NonprincipalAbelV3
   Original SHA256: f22a4636189751e17eb2562c27e90c6b3ebbd3d95211f78ddcbd2de03ddc27e9 -/
section P2MFinalSource021

open Finset Filter MeasureTheory Set Complex Asymptotics
open scoped Topology
set_option autoImplicit false

namespace RiemannVonMangoldt

/-- The exact Icc indexing used by Mathlib's Abel integral. -/
theorem nonprincipal_Icc_sum_bound (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)‖ ≤ (q : ℝ) := by
  have he : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by ext k; simp
  rw [he, Finset.sum_Ico_eq_sum_range]
  simpa [Nat.add_comm] using dirichlet_nonprincipal_partial_sum_norm_le_level q χ hχ n

noncomputable def abelPartial (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod q)

noncomputable def abelCutoff (A : ℝ → ℂ) : ℝ → ℂ := (Set.Ioi (1 : ℝ)).indicator A

theorem abelPartial_locallyIntegrable (q : ℕ) (χ : DirichletCharacter ℂ q) :
    LocallyIntegrableOn (abelPartial q χ) (Set.Ioi (0 : ℝ)) := by
  have h : LocallyIntegrableOn (abelPartial q χ) (Set.Ici (0 : ℝ)) := by
    unfold abelPartial
    simpa using
      (locallyIntegrableOn_mul_sum_Icc (c := fun k : ℕ => χ (k : ZMod q))
        (m := 1) (a := (0 : ℝ)) le_rfl (locallyIntegrableOn_const (1 : ℂ)))
  exact h.mono_set Set.Ioi_subset_Ici_self

/-- Holomorphy from the actual Mellin differentiation theorem, not formal
conditional summation outside the region of absolute convergence. -/
theorem abel_mellin_differentiable (A : ℝ → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hA : ∀ t, ‖A t‖ ≤ C)
    (hloc : LocallyIntegrableOn A (Set.Ioi (0 : ℝ)))
    (s : ℂ) (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => mellin (abelCutoff A) (-z)) s := by
  have hcut : LocallyIntegrableOn (abelCutoff A) (Set.Ioi (0 : ℝ)) := by
    rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
    intro K hK hcompact
    have h := hloc.integrableOn_compact_subset hK hcompact
    apply Integrable.mono h
    · exact h.aestronglyMeasurable.indicator measurableSet_Ioi
    · filter_upwards with t
      by_cases ht : t ∈ Set.Ioi (1 : ℝ)
      · simp [abelCutoff, Set.indicator_of_mem ht]
      · simp [abelCutoff, Set.indicator_of_notMem ht]
  have htop : abelCutoff A =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
    refine isBigO_iff.mpr ⟨C, Filter.Eventually.of_forall ?_⟩
    intro t
    by_cases ht : t ∈ Set.Ioi (1 : ℝ)
    · simpa [abelCutoff, Set.indicator_of_mem ht, Real.norm_eq_abs] using hA t
    · simp [abelCutoff, Set.indicator_of_notMem ht, Real.norm_eq_abs, hC]
  have hbot : abelCutoff A =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-(-s.re - 1))) := by
    apply isBigO_iff.mpr
    refine ⟨1, ?_⟩
    have hlt : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
    filter_upwards [hlt] with t ht
    simp [abelCutoff, Set.indicator_of_notMem (show t ∉ Set.Ioi (1 : ℝ) by exact not_lt_of_ge ht.le)]
  exact (mellin_differentiableAt_of_isBigO_rpow hcut htop (by simpa using hs)
    hbot (by simp : -s.re - 1 < (-s).re)).comp s (differentiableAt_id.neg)

/-- Exact restriction to (1, infinity), with the original exponent. -/
theorem abel_mellin_eq_integral (A : ℝ → ℂ) (s : ℂ) :
    mellin (abelCutoff A) (-s) =
      ∫ t : ℝ in Set.Ioi 1, A t * (t : ℂ) ^ (-(s + 1)) := by
  unfold mellin abelCutoff
  calc
    _ = ∫ t : ℝ in Set.Ioi (0 : ℝ),
        (Set.Ioi (1 : ℝ)).indicator (fun t => A t * (t : ℂ) ^ (-(s + 1))) t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      by_cases h : t ∈ Set.Ioi (1 : ℝ)
      · simp only [Set.indicator_of_mem h, smul_eq_mul]
        rw [mul_comm, show -s - 1 = -(s + 1) by ring]
      · simp [Set.indicator_of_notMem h]
    _ = _ := by
      rw [setIntegral_indicator measurableSet_Ioi,
        Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))]

theorem nonprincipal_abel_integral (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    χ.LFunction s = s * ∫ t : ℝ in Set.Ioi 1,
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(s + 1)) := by
  let A := abelPartial q χ
  let F : ℂ → ℂ := fun z => z * mellin (abelCutoff A) (-z)
  have hA : ∀ t, ‖A t‖ ≤ (q : ℝ) :=
    fun t => nonprincipal_Icc_sum_bound q χ hχ ⌊t⌋₊
  have hdiff : DifferentiableOn ℂ F {z | 0 < z.re} := by
    intro z hz
    exact (differentiableAt_id.mul (abel_mellin_differentiable A (q : ℝ)
      (Nat.cast_nonneg q) hA (abelPartial_locallyIntegrable q χ) z hz)).differentiableWithinAt
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hEq : Set.EqOn χ.LFunction F {z : ℂ | 0 < z.re} := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      ((χ.differentiable_LFunction hχ).differentiableOn.analyticOnNhd hopen)
      (hdiff.analyticOnNhd hopen) (convex_halfSpace_re_gt 0).isPreconnected
      (show (2 : ℂ) ∈ {z : ℂ | 0 < z.re} by norm_num) ?_
    have hu : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
    filter_upwards [hu] with z hz
    have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ (0 : ℝ)) := by
      refine isBigO_iff.mpr ⟨(q : ℝ), Filter.Eventually.of_forall ?_⟩
      intro n
      simpa using nonprincipal_Icc_sum_bound q χ hχ n
    rw [χ.LFunction_eq_LSeries hz, LSeries_eq_mul_integral _ le_rfl
      (show (0 : ℝ) < z.re from lt_trans zero_lt_one hz)
      (χ.LSeriesSummable_of_one_lt_re hz) hO]
    simp [F, A, abel_mellin_eq_integral, abelPartial]
  simpa [F, A, abel_mellin_eq_integral, abelPartial] using hEq hs

end RiemannVonMangoldt
end P2MFinalSource021

/- Source module: NonprincipalGrowthV1
   Original SHA256: f03697f6dcabb5939a8dabe5efb7cfc75ade8c9bb97343db0cb26d6f731c6853 -/
section P2MFinalSource022

open Finset Filter MeasureTheory Set Complex Asymptotics
open scoped Topology
set_option autoImplicit false

namespace RiemannVonMangoldt

/-- Quantitative absolute integrability for the genuine Abel kernel. -/
theorem abel_integrable_and_norm_bound (A : ℝ → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hA : ∀ t, ‖A t‖ ≤ C)
    (hloc : LocallyIntegrableOn A (Set.Ioi (0 : ℝ)))
    (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => A t * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) ∧
      ‖∫ t : ℝ in Set.Ioi 1, A t * (t : ℂ) ^ (-(s + 1))‖ ≤ C / s.re := by
  let a : ℝ := -(s.re + 1)
  let f : ℝ → ℂ := fun t => A t * (t : ℂ) ^ (-(s + 1))
  let g : ℝ → ℝ := fun t => C * t ^ a
  have ha : a < -1 := by dsimp [a]; linarith
  have hg : IntegrableOn g (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt ha zero_lt_one).const_mul C
  have hdom : ∀ t ∈ Set.Ioi (1 : ℝ), ‖f t‖ ≤ g t := by
    intro t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    simp only [f, g, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0,
      neg_re, add_re, one_re, a]
    exact mul_le_mul_of_nonneg_right (hA t) (Real.rpow_nonneg ht0.le _)
  have hmeasA := (hloc.mono_set (Set.Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
  have hmeasPow : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (-(s + 1)))
      (volume.restrict (Set.Ioi (1 : ℝ))) :=
    (integrableOn_Ioi_cpow_of_lt (by simp; linarith : (-(s + 1)).re < -1) zero_lt_one).aestronglyMeasurable
  have hdomAE : ∀ᵐ t ∂volume.restrict (Set.Ioi (1 : ℝ)), ‖f t‖ ≤ g t :=
    (ae_restrict_mem measurableSet_Ioi).mono hdom
  have hf : IntegrableOn f (Set.Ioi 1) :=
    Integrable.mono' hg (hmeasA.mul hmeasPow) hdomAE
  refine ⟨hf, ?_⟩
  calc
    ‖∫ t : ℝ in Set.Ioi 1, f t‖ ≤ ∫ t : ℝ in Set.Ioi 1, ‖f t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Set.Ioi 1, g t := integral_mono_ae hf.norm hg hdomAE
    _ = C / s.re := by
      dsimp [g]
      rw [integral_const_mul, integral_Ioi_rpow_of_lt ha zero_lt_one, Real.one_rpow]
      have he : a + 1 = -s.re := by dsimp [a]; ring
      rw [he]
      ring

/-- Uniform, original-definition growth bound on the entire right half-plane. -/
theorem nonprincipal_LFunction_norm_le (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    ‖χ.LFunction s‖ ≤ (q : ℝ) * ‖s‖ / s.re := by
  have h := (abel_integrable_and_norm_bound (abelPartial q χ) (q : ℝ)
    (Nat.cast_nonneg q) (fun t => nonprincipal_Icc_sum_bound q χ hχ ⌊t⌋₊)
    (abelPartial_locallyIntegrable q χ) s hs).2
  rw [nonprincipal_abel_integral q χ hχ s hs, norm_mul]
  have h' := mul_le_mul_of_nonneg_left h (norm_nonneg s)
  unfold abelPartial at h'
  calc
    _ ≤ ‖s‖ * ((q : ℝ) / s.re) := h'
    _ = _ := by ring

end RiemannVonMangoldt
end P2MFinalSource022

/- Source module: PrincipalGrowthV2
   Original SHA256: 1e0dd1d53002fb6efdc7c73e93382c68e6952250f3176a94e7144aa8613eccb5 -/
section P2MFinalSource023

open Finset Filter MeasureTheory Set Complex Asymptotics
open scoped Topology
set_option autoImplicit false

namespace RiemannVonMangoldt

noncomputable def fractionalPartC (t : ℝ) : ℂ := ((Int.fract t : ℝ) : ℂ)

theorem fractionalPartC_norm_le (t : ℝ) : ‖fractionalPartC t‖ ≤ 1 := by
  rw [fractionalPartC, Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg t)]
  exact (Int.fract_lt_one t).le

theorem fractionalPartC_locallyIntegrable :
    LocallyIntegrableOn fractionalPartC (Set.Ioi (0 : ℝ)) := by
  refine (locallyIntegrableOn_const (1 : ℝ)).mono ?_ ?_
  · unfold fractionalPartC
    exact (Complex.continuous_ofReal.measurable.comp (measurable_fract : Measurable (Int.fract : ℝ → ℝ))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by simpa using fractionalPartC_norm_le t)

/-- Classical zeta Abel formula on the actual absolute convergence half-plane. -/
theorem riemannZeta_abel_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = s / (s - 1) -
      s * ∫ t : ℝ in Set.Ioi 1, fractionalPartC t * (t : ℂ) ^ (-(s + 1)) := by
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (1 : ℂ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
    refine isBigO_iff.mpr ⟨1, Filter.Eventually.of_forall ?_⟩
    intro n
    simp [Nat.card_Icc]
  have hrepr := LSeries_eq_mul_integral (fun _ : ℕ => (1 : ℂ)) zero_le_one hs
    (LSeriesSummable_one_iff.mpr hs) hO
  have hrepr' : riemannZeta s = s * ∫ t : ℝ in Set.Ioi 1,
      ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    rw [← LSeries_one_eq_riemannZeta hs]
    change LSeries (fun _ : ℕ => (1 : ℂ)) s = _
    simpa [Nat.card_Icc] using hrepr
  have hsplit (t : ℝ) (ht : t ∈ Set.Ioi (1 : ℝ)) :
      ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1)) =
        (t : ℂ) ^ (-s) - fractionalPartC t * (t : ℂ) ^ (-(s + 1)) := by
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hfloor : ((⌊t⌋₊ : ℕ) : ℂ) = (t : ℂ) - fractionalPartC t := by
      unfold fractionalPartC Int.fract
      rw [Complex.ofReal_sub, sub_sub_cancel]
      exact_mod_cast Int.natCast_floor_eq_floor ht0.le
    rw [hfloor, sub_mul]
    have he : (1 : ℂ) + -(s + 1) = -s := by ring
    have hp : (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = (t : ℂ) ^ (-s) := by
      calc
        _ = (t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (-(s + 1)) := by rw [Complex.cpow_one]
        _ = _ := by rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht0.ne'), he]
    rw [hp]
  rw [hrepr', setIntegral_congr_fun measurableSet_Ioi hsplit,
    integral_sub (integrableOn_Ioi_cpow_of_lt (by simpa using hs) zero_lt_one)
      (abel_integrable_and_norm_bound fractionalPartC 1 zero_le_one
        fractionalPartC_norm_le fractionalPartC_locallyIntegrable s
        (zero_lt_one.trans hs)).1,
    integral_Ioi_cpow_of_lt (by simpa using hs) zero_lt_one, Complex.ofReal_one, Complex.one_cpow]
  have he : -s + 1 = -(s - 1) := by ring
  rw [he, neg_div_neg_eq]
  ring

/-- Continue the fractional-part integral using the genuine entire regularization. -/
theorem riemannZeta_abel_right_half_plane (s : ℂ) (hs : 0 < s.re) (hne : s ≠ 1) :
    riemannZeta s = s / (s - 1) -
      s * ∫ t : ℝ in Set.Ioi 1, fractionalPartC t * (t : ℂ) ^ (-(s + 1)) := by
  let F : ℂ → ℂ := fun z => 1 - z * mellin (abelCutoff fractionalPartC) (-z)
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hdiff : DifferentiableOn ℂ F {z | 0 < z.re} := by
    intro z hz
    exact ((differentiableAt_const _).sub (differentiableAt_id.mul
      (abel_mellin_differentiable fractionalPartC 1 zero_le_one fractionalPartC_norm_le
        fractionalPartC_locallyIntegrable z hz))).differentiableWithinAt
  have hEq : Set.EqOn riemannZeta₀ F {z : ℂ | 0 < z.re} := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (differentiable_riemannZeta₀.differentiableOn.analyticOnNhd hopen)
      (hdiff.analyticOnNhd hopen) (convex_halfSpace_re_gt 0).isPreconnected
      (show (2 : ℂ) ∈ {z : ℂ | 0 < z.re} by norm_num) ?_
    have hu : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
    filter_upwards [hu] with z hz
    have hne' : z ≠ 1 := by intro h; subst z; simp at hz
    rw [riemannZeta₀, if_neg hne', riemannZeta_abel_of_one_lt_re z hz]
    dsimp [F]
    rw [abel_mellin_eq_integral]
    field_simp [sub_ne_zero.mpr hne']
    <;> ring
  have h := hEq hs
  dsimp [F] at h
  rw [abel_mellin_eq_integral] at h
  rw [riemannZeta_eq_inv_sub_add hne, h]
  field_simp [sub_ne_zero.mpr hne]
  <;> ring

/-- Principal modulus-one growth with a separate, explicit pole term. -/
theorem mod_one_LFunction_norm_le (χ : DirichletCharacter ℂ 1)
    (s : ℂ) (hs : 0 < s.re) (hne : s ≠ 1) :
    ‖χ.LFunction s‖ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re := by
  rw [DirichletCharacter.LFunction_modOne_eq, riemannZeta_abel_right_half_plane s hs hne]
  have hb := (abel_integrable_and_norm_bound fractionalPartC 1 zero_le_one
    fractionalPartC_norm_le fractionalPartC_locallyIntegrable s hs).2
  calc
    _ ≤ ‖s / (s - 1)‖ + ‖s * ∫ t : ℝ in Set.Ioi 1,
        fractionalPartC t * (t : ℂ) ^ (-(s + 1))‖ := norm_sub_le _ _
    _ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ * (1 / s.re) := by
      rw [norm_div, norm_mul]
      exact add_le_add_right (mul_le_mul_of_nonneg_left hb (norm_nonneg s)) _
    _ = _ := by ring

end RiemannVonMangoldt
end P2MFinalSource023

/- Source module: UniformLowerAnchorV2
   Original SHA256: 8f55fb5619564196d0bf3338cc714f08bda19f4fb0aea95a3d767a2f5698d608 -/
section P2MFinalSource024

open scoped LSeries.notation ArithmeticFunction.Moebius
set_option autoImplicit false

namespace RiemannVonMangoldt

/-- Source candidate: fixed lower anchor independent of level and height.
The inverse Dirichlet series identity is existing Mathlib, not a new result. -/
theorem dirichlet_LFunction_uniform_lower_anchor :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
        s.re = 3 / 2 → c ≤ ‖χ.LFunction s‖ := by
  let z : ℂ := ((3 / 2 : ℝ) : ℂ)
  have hz : 1 < z.re := by norm_num [z]
  let A : ℝ := ∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) z n‖
  have hA : 0 ≤ A := tsum_nonneg (fun n => norm_nonneg _)
  have hK : 0 < A + 1 := by linarith
  refine ⟨1 / (A + 1), one_div_pos.mpr hK, ?_⟩
  intro q _ χ s hs
  have hs1 : 1 < s.re := by linarith
  have hsz : z.re ≤ s.re := by norm_num [z, hs]
  have hsum : LSeriesSummable (↗χ * ↗μ) s :=
    χ.LSeriesSummable_mul (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs1)
  have hone : LSeriesSummable (1 : ℕ → ℂ) z :=
    LSeriesSummable_one_iff.mpr hz
  have hterm (n : ℕ) :
      ‖LSeries.term (↗χ * ↗μ) s n‖ ≤
        ‖LSeries.term (1 : ℕ → ℂ) z n‖ := by
    calc
      _ ≤ ‖LSeries.term (1 : ℕ → ℂ) s n‖ := by
        apply LSeries.norm_term_le
        have hm : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
          norm_cast
          exact ArithmeticFunction.abs_moebius_le_one
        simp only [Pi.mul_apply, Pi.one_apply, norm_one, norm_mul]
        exact mul_le_one₀ (χ.norm_le_one n) (norm_nonneg _) hm
      _ ≤ _ := LSeries.norm_term_le_of_re_le_re _ hsz n
  have hbound : ‖LSeries (↗χ * ↗μ) s‖ ≤ A := by
    calc
      _ ≤ ∑' n : ℕ, ‖LSeries.term (↗χ * ↗μ) s n‖ :=
        norm_tsum_le_tsum_norm hsum.norm
      _ ≤ A := Summable.tsum_le_tsum hterm hsum.norm hone.norm
  have hid := DirichletCharacter.LSeries.mul_mu_eq_one χ hs1
  rw [← χ.LFunction_eq_LSeries hs1] at hid
  have hprod : ‖χ.LFunction s‖ * ‖LSeries (↗χ * ↗μ) s‖ = 1 := by
    rw [← norm_mul, hid, norm_one]
  apply (div_le_iff₀ hK).2
  calc
    1 = ‖χ.LFunction s‖ * ‖LSeries (↗χ * ↗μ) s‖ := hprod.symm
    _ ≤ ‖χ.LFunction s‖ * (A + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)

end RiemannVonMangoldt

end P2MFinalSource024

/- Source module: PrimitiveDiskGrowthV3
   Original SHA256: 3930861ccdcbdc73e8f59ff724f30747d3d6d87953a7c51fc241f1b3da753fe8 -/
section P2MFinalSource025

open Complex Set Metric
set_option autoImplicit false

namespace RiemannVonMangoldt

noncomputable def horizontalCenter (t : ℝ) : ℂ := (3/2 : ℂ) + (t : ℂ) * I

theorem primitive_principal_level_one (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hχ : χ = 1) : q = 1 := by
  have h := (DirichletCharacter.isPrimitive_def χ).mp hp
  rw [hχ, DirichletCharacter.conductor_one] at h
  exact h.symm

theorem horizontalDisk_geometry (t : ℝ) (ht : 3 ≤ |t|)
    (z : ℂ) (hz : ‖z - horizontalCenter t‖ ≤ 5/4) :
    1/4 ≤ z.re ∧ 1 ≤ ‖z - 1‖ ∧ ‖z‖ ≤ |t| + 3 := by
  have hr := Complex.abs_re_le_norm (z - horizontalCenter t)
  have hi := Complex.abs_im_le_norm (z - horizontalCenter t)
  have cr : (horizontalCenter t).re = 3/2 := by
    norm_num [horizontalCenter, Complex.add_re, Complex.mul_re, Complex.div_re]
  have ci : (horizontalCenter t).im = t := by
    norm_num [horizontalCenter, Complex.add_im, Complex.mul_im, Complex.div_im]
  rw [Complex.sub_re, cr] at hr
  rw [Complex.sub_im, ci] at hi
  have hr' := (abs_le.mp (hr.trans hz)).1
  have hi' : |z.im - t| ≤ 5/4 := hi.trans hz
  have htri : |t| ≤ |z.im| + |z.im - t| := by
    have h2 := abs_sub_le t z.im 0
    rw [sub_zero, sub_zero, abs_sub_comm t z.im] at h2
    linarith
  have hnorm := Complex.abs_im_le_norm (z - 1)
  rw [Complex.sub_im, Complex.one_im, sub_zero] at hnorm
  have hc : ‖horizontalCenter t‖ ≤ 3/2 + |t| := by
    unfold horizontalCenter
    calc
      _ ≤ ‖(3/2 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = _ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
        norm_num
  have hzn : ‖z‖ ≤ ‖z - horizontalCenter t‖ + ‖horizontalCenter t‖ := by
    convert norm_add_le (z - horizontalCenter t) (horizontalCenter t) using 1 <;> ring
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Absolute growth on a fixed disk, uniformly for all nonzero levels and primitive characters.
The only principal primitive character has level one. The disk avoids the pole. -/
theorem primitive_LFunction_fixed_disk_growth (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive)
    (t : ℝ) (ht : 3 ≤ |t|) (z : ℂ)
    (hz : ‖z - horizontalCenter t‖ ≤ 5/4) :
    ‖χ.LFunction z‖ ≤ 5 * (q : ℝ) * (|t| + 3) := by
  obtain ⟨hre, hpole, hn⟩ := horizontalDisk_geometry t ht z hz
  have hs : 0 < z.re := by linarith
  have hn0 := norm_nonneg z
  have hq : 1 ≤ (q : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hb : ∀ a : ℝ, 0 ≤ a → a / z.re ≤ 4 * a := by
    intro a ha
    apply (div_le_iff₀ hs).2
    nlinarith [mul_nonneg ha (show 0 ≤ z.re - 1/4 by linarith)]
  by_cases hχ : χ = 1
  · have hlevel := primitive_principal_level_one q χ hp hχ
    subst q
    have hne : z ≠ 1 := by
      intro h
      subst z
      norm_num at hpole
    have ha := mod_one_LFunction_norm_le χ z hs hne
    have hp0 : 0 < ‖z - 1‖ := by linarith
    have hdiv : ‖z‖ / ‖z - 1‖ ≤ ‖z‖ := by
      apply (div_le_iff₀ hp0).2
      nlinarith [mul_nonneg hn0 (show 0 ≤ ‖z - 1‖ - 1 by linarith)]
    simp only [Nat.cast_one, mul_one]
    linarith [hb ‖z‖ hn0]
  · have ha := nonprincipal_LFunction_norm_le q χ hχ z hs
    have hqn : 0 ≤ (q : ℝ) * ‖z‖ := mul_nonneg (Nat.cast_nonneg q) hn0
    have h1 := hb ((q : ℝ) * ‖z‖) hqn
    have h2 := mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg q : 0 ≤ (q : ℝ))
    nlinarith [mul_nonneg (Nat.cast_nonneg q : 0 ≤ (q : ℝ)) (show 0 ≤ |t| + 3 by linarith)]


end RiemannVonMangoldt
end P2MFinalSource025

/- Source module: ConjugateReflectionV1
   Original SHA256: 7bb388c169a17a99e70a840887450d5b8b5d57c43845e2198e3c3053828e12de -/
section P2MFinalSource026

open Complex Filter Set
open scoped ComplexConjugate Topology
set_option autoImplicit false

namespace RiemannVonMangoldt

/-- Schwarz reflection of a holomorphic function, without a real-valued boundary assumption. -/
theorem hasDerivAt_conjugate_reflection (f : ℂ → ℂ) (a z : ℂ)
    (h : HasDerivAt f a (conj z)) :
    HasDerivAt (fun w => conj (f (conj w))) (conj a) z := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hc : Tendsto (conj : ℂ → ℂ) (𝓝[≠] z) (𝓝[≠] (conj z)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨Complex.continuous_conj.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin (a := z) (s := {z}ᶜ)] with w hw
    simp only [mem_compl_iff, mem_singleton_iff] at hw ⊢
    exact fun he => hw (by simpa using congrArg conj he)
  have hs := h.tendsto_slope.comp hc
  have hh := Complex.continuous_conj.continuousAt.tendsto.comp hs
  convert hh using 1
  ext w
  simp [Function.comp_def, slope_def_field, map_div₀, map_sub]

end RiemannVonMangoldt
end P2MFinalSource026

/- Source module: ReflectedJensenV3
   Original SHA256: 6171a5c7fab145fd2776424c9b66bd0733bb4bb554389baad0eb19dfe10c6325 -/
section P2MFinalSource027

open Complex Filter Set Metric MeromorphicOn
open scoped ComplexConjugate Topology
set_option autoImplicit false

namespace RiemannVonMangoldt

noncomputable def normalizedHorizontal {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) (w : ℂ) : ℂ :=
  χ.LFunction (horizontalCenter t + w) / χ.LFunction (horizontalCenter t)

noncomputable def reflectedHorizontal {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) (w : ℂ) : ℂ :=
  (normalizedHorizontal χ t w + conj (normalizedHorizontal χ t (conj w))) / 2

theorem reflectedHorizontal_real {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t x : ℝ) :
    reflectedHorizontal χ t (x : ℂ) = ((normalizedHorizontal χ t (x : ℂ)).re : ℂ) := by
  rw [reflectedHorizontal, Complex.conj_ofReal]
  apply Complex.ext <;> simp [Complex.div_re, Complex.div_im, Complex.add_re, Complex.add_im] <;> ring

theorem normalizedHorizontal_differentiableAt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) (ht : 3 ≤ |t|)
    (w : ℂ) (hw : ‖w‖ < 3/2) :
    DifferentiableAt ℂ (normalizedHorizontal χ t) w := by
  have ci : (horizontalCenter t).im = t := by
    norm_num [horizontalCenter, Complex.add_im, Complex.mul_im, Complex.div_im]
  have hne : horizontalCenter t + w ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    rw [Complex.add_im, ci, Complex.one_im] at hi
    have he : w.im = -t := by linarith
    have hh := Complex.abs_im_le_norm w
    rw [he, abs_neg] at hh
    linarith
  unfold normalizedHorizontal
  exact ((DirichletCharacter.differentiableAt_LFunction χ _ (Or.inl hne)).comp w
    ((differentiableAt_const _).add differentiableAt_id)).div_const _

theorem reflectedHorizontal_analytic {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) (ht : 3 ≤ |t|) :
    AnalyticOnNhd ℂ (reflectedHorizontal χ t) (closedBall 0 (5/4)) := by
  have hd : DifferentiableOn ℂ (reflectedHorizontal χ t) (ball 0 (3/2)) := by
    intro w hw
    have hwn : ‖w‖ < 3/2 := by simpa [mem_ball, dist_eq_norm] using hw
    have h1 := normalizedHorizontal_differentiableAt χ t ht w hwn
    have h2 := normalizedHorizontal_differentiableAt χ t ht (conj w)
      (by simpa [Complex.norm_conj] using hwn)
    have h3 := (hasDerivAt_conjugate_reflection (normalizedHorizontal χ t)
      (deriv (normalizedHorizontal χ t) (conj w)) w h2.hasDerivAt).differentiableAt
    exact ((h1.add h3).div_const 2).differentiableWithinAt
  exact (hd.analyticOnNhd isOpen_ball).mono (closedBall_subset_ball (by norm_num))

theorem reflectedHorizontal_center {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) (h : χ.LFunction (horizontalCenter t) ≠ 0) :
    reflectedHorizontal χ t 0 = 1 := by
  simp [reflectedHorizontal, normalizedHorizontal, h]

theorem normalizedHorizontal_norm_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive)
    (t : ℝ) (ht : 3 ≤ |t|) (c : ℝ) (hc : 0 < c)
    (ha : c ≤ ‖χ.LFunction (horizontalCenter t)‖)
    (w : ℂ) (hw : ‖w‖ ≤ 5/4) :
    ‖normalizedHorizontal χ t w‖ ≤ (5 * (q : ℝ) * (|t| + 3)) / c := by
  have hg := primitive_LFunction_fixed_disk_growth q χ hp t ht (horizontalCenter t + w)
    (by simpa only [add_sub_cancel_left] using hw)
  rw [normalizedHorizontal, norm_div]
  exact div_le_div_of_nonneg_right hg (le_of_lt (hc.trans_le ha)) |>.trans
    (div_le_div_of_nonneg_left (by positivity) hc ha)

theorem reflectedHorizontal_norm_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive)
    (t : ℝ) (ht : 3 ≤ |t|) (c : ℝ) (hc : 0 < c)
    (ha : c ≤ ‖χ.LFunction (horizontalCenter t)‖)
    (w : ℂ) (hw : ‖w‖ ≤ 5/4) :
    ‖reflectedHorizontal χ t w‖ ≤ (5 * (q : ℝ) * (|t| + 3)) / c := by
  have h1 := normalizedHorizontal_norm_bound χ hp t ht c hc ha w hw
  have h2 := normalizedHorizontal_norm_bound χ hp t ht c hc ha (conj w)
    (by simpa [Complex.norm_conj] using hw)
  rw [reflectedHorizontal, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
  apply (div_le_iff₀ (by norm_num : (0:ℝ) < 2)).2
  have hsum := norm_add_le (normalizedHorizontal χ t w) (conj (normalizedHorizontal χ t (conj w)))
  rw [Complex.norm_conj] at hsum
  linarith

/-- Jensen applied to the reflected real part of the normalized L-function, not merely
to zeros of L itself. Its zeros on the real horizontal segment are real-part crossings. -/
theorem reflectedHorizontal_jensen_uniform :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (hp : χ.IsPrimitive) (t : ℝ), 3 ≤ |t| →
      (↑(∑ᶠ u, divisor (reflectedHorizontal χ t) (closedBall 0 1) u) : ℝ) ≤
        Real.log (1 + (5 * (q : ℝ) * (|t| + 3)) / c) / Real.log (5/4) := by
  obtain ⟨c, hc, hlow⟩ := dirichlet_LFunction_uniform_lower_anchor
  refine ⟨c, hc, ?_⟩
  intro q _ χ hp t ht
  have hcenter : (horizontalCenter t).re = 3/2 := by
    norm_num [horizontalCenter, Complex.add_re, Complex.mul_re, Complex.div_re]
  have ha := hlow q χ (horizontalCenter t) hcenter
  have hne : χ.LFunction (horizontalCenter t) ≠ 0 := by
    exact norm_pos_iff.mp (hc.trans_le ha)
  have h0 := reflectedHorizontal_center χ t hne
  have han := reflectedHorizontal_analytic χ t ht
  let M : ℝ := 1 + (5 * (q : ℝ) * (|t| + 3)) / c
  have hM : 1 ≤ M := by
    dsimp [M]
    have hh : 0 ≤ (5 * (q : ℝ) * (|t| + 3)) / c := by positivity
    linarith
  have hb : ∀ z ∈ sphere (0 : ℂ) |(5/4 : ℝ)|, ‖reflectedHorizontal χ t z‖ ≤ M := by
    intro z hz
    have hzn : ‖z‖ ≤ 5/4 := by
      rw [mem_sphere, dist_eq_norm, sub_zero, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 5/4)] at hz
      exact hz.le
    have h := reflectedHorizontal_norm_bound χ hp t ht c hc ha z hzn
    dsimp [M]
    linarith
  have h := AnalyticOnNhd.sum_divisor_le (c := (0 : ℂ)) (r := (1 : ℝ)) (R := (5/4 : ℝ))
    (M := M) (f := reflectedHorizontal χ t) (by norm_num) (by norm_num) hM
    (by simpa only [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 5/4)] using han) (by rw [h0]; norm_num) hb
  rw [abs_one] at h
  simpa [M, h0] using h


end RiemannVonMangoldt
end P2MFinalSource027

/- Source module: ReflectedCrossingsV3
   Original SHA256: ffa53b882123ee76b19ee71ed609361ca643aa39599b6ae6b0cd82103e339da9 -/
section P2MFinalSource028

open Complex Filter Set Metric MeromorphicOn
open scoped ComplexConjugate Topology BigOperators
set_option autoImplicit false

namespace RiemannVonMangoldt

/-- A nontrivial analytic function's real zeros in the unit segment
are supported by its positive integral divisor on the unit disk. -/
theorem reflected_crossing_card_le_divisor
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (closedBall 0 1))
    (h0 : f 0 ≠ 0) :
    let S := {x : ℝ | x ∈ Icc (-1) 0 ∧ f (x : ℂ) = 0}
    S.Finite ∧ (S.ncard : ℤ) ≤ ∑ᶠ u, divisor f (closedBall 0 1) u := by
  classical
  dsimp
  let S := {x : ℝ | x ∈ Icc (-1) 0 ∧ f (x : ℂ) = 0}
  let D := divisor f (closedBall 0 1)
  have hfD : D.support.Finite := D.finiteSupport (isCompact_closedBall 0 1)
  have hcenter : (0 : ℂ) ∈ closedBall 0 1 := by simp
  have horder0 : analyticOrderAt f 0 ≠ ⊤ := by
    rw [(hf 0 hcenter).analyticOrderAt_eq_zero.mpr h0]
    exact ENat.natCast_ne_top 0
  have hi : Function.Injective (fun x : ℝ => (x : ℂ)) := Complex.ofReal_injective
  have hmap : ∀ x ∈ S, (x : ℂ) ∈ D.support := by
    intro x hx
    have hx' : x ∈ Icc (-1 : ℝ) 0 ∧ f (x : ℂ) = 0 := hx
    have hxball : (x : ℂ) ∈ closedBall 0 1 := by
      rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨hx'.1.1, hx'.1.2.trans (by norm_num)⟩
    have ho := hf.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_closedBall hcenter hxball horder0
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp ho
    have hne : analyticOrderAt f (x : ℂ) ≠ 0 :=
      (hf _ hxball).analyticOrderAt_ne_zero.mpr hx'.2
    have hn0 : n ≠ 0 := by
      intro h
      apply hne
      simpa [h] using hn.symm
    have hD : D (x : ℂ) = (n : ℤ) := by
      change divisor f (closedBall 0 1) (x : ℂ) = _
      rw [hf.divisor_apply hxball, ← hn]
      simp
    rw [Function.mem_support, hD]
    exact_mod_cast hn0
  have hS : S.Finite := (hfD.subset (by
    rintro _ ⟨x, hx, rfl⟩
    exact hmap x hx)).of_finite_image hi.injOn
  have hcard : S.ncard ≤ D.support.ncard :=
    Set.ncard_le_ncard_of_injOn (fun x : ℝ => (x : ℂ)) hmap hi.injOn hfD
  have hsum : (D.support.ncard : ℤ) ≤ ∑ᶠ u, D u := by
    rw [Set.ncard_eq_toFinset_card _ hfD,
      finsum_eq_finsetSum_of_support_subset D (s := hfD.toFinset) (by simpa only [Set.Finite.coe_toFinset] using (Subset.rfl : D.support ⊆ D.support))]
    calc
      (hfD.toFinset.card : ℤ) = ∑ _u ∈ hfD.toFinset, (1 : ℤ) := by simp
      _ ≤ ∑ u ∈ hfD.toFinset, D u := by
        apply Finset.sum_le_sum
        intro u hu
        have hnonzero : D u ≠ 0 := by
          exact (Function.mem_support.mp (hfD.mem_toFinset.mp hu))
        have hnn : 0 ≤ D u := hf.divisor_nonneg u
        omega
  exact ⟨hS, (Int.ofNat_le.mpr hcard).trans hsum⟩

theorem reflectedHorizontal_distinct_crossings_uniform :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (hp : χ.IsPrimitive) (t : ℝ), 3 ≤ |t| →
      let S := {x : ℝ | x ∈ Icc (-1) 0 ∧ (normalizedHorizontal χ t (x : ℂ)).re = 0}
      S.Finite ∧ (S.ncard : ℝ) ≤
        Real.log (1 + (5 * (q : ℝ) * (|t| + 3)) / c) / Real.log (5/4) := by
  obtain ⟨c, hc, hj⟩ := reflectedHorizontal_jensen_uniform
  refine ⟨c, hc, ?_⟩
  intro q _ χ hp t ht
  obtain ⟨a, ha, hlow⟩ := dirichlet_LFunction_uniform_lower_anchor
  have hcenter : (horizontalCenter t).re = 3/2 := by
    norm_num [horizontalCenter, Complex.add_re, Complex.mul_re, Complex.div_re]
  have hne : χ.LFunction (horizontalCenter t) ≠ 0 :=
    norm_pos_iff.mp (ha.trans_le (hlow q χ (horizontalCenter t) hcenter))
  have hf := (reflectedHorizontal_analytic χ t ht).mono
    (closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 5/4))
  have h0 : reflectedHorizontal χ t 0 ≠ 0 := by
    rw [reflectedHorizontal_center χ t hne]
    exact one_ne_zero
  have h := reflected_crossing_card_le_divisor (reflectedHorizontal χ t) hf h0
  have hs : {x : ℝ | x ∈ Icc (-1) 0 ∧ reflectedHorizontal χ t (x : ℂ) = 0} =
      {x : ℝ | x ∈ Icc (-1) 0 ∧ (normalizedHorizontal χ t (x : ℂ)).re = 0} := by
    ext x
    simp [reflectedHorizontal_real]
  dsimp at h ⊢
  rw [hs] at h
  refine ⟨h.1, ?_⟩
  have hcast : (({x : ℝ | x ∈ Icc (-1) 0 ∧ (normalizedHorizontal χ t (x : ℂ)).re = 0}).ncard : ℝ)
      ≤ (↑(∑ᶠ u, divisor (reflectedHorizontal χ t) (closedBall 0 1) u) : ℝ) := by
    exact_mod_cast h.2
  exact hcast.trans (hj q χ hp t ht)


end RiemannVonMangoldt
end P2MFinalSource028

/- Source module: ContinuousArgumentCountV2
   Original SHA256: e12ed70cc8590db485a15cf2139cc25caee75825255edb991a7045c896779f4e -/
section P2MFinalSource029

open Complex Filter Set Metric
open scoped Topology
set_option autoImplicit false

namespace RiemannVonMangoldt

/-- A continuous real function traversing integer levels must visit distinct
points of any finite set containing all of its integer-level crossings.
The result bounds net change, not total variation. -/
theorem continuous_integer_level_net_change
    (g : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b))
    (S : Set ℝ) (hS : S.Finite)
    (hlevel : ∀ x ∈ Icc a b, ∀ k : ℤ, g x = (k : ℝ) → x ∈ S) :
    |g b - g a| ≤ (S.ncard : ℝ) + 1 := by
  classical
  let u := min (g a) (g b)
  let v := max (g a) (g b)
  let A : Finset ℤ := Finset.Icc ⌈u⌉ ⌊v⌋
  have huv : u ≤ v := min_le_max
  have hiv : Icc u v ⊆ g '' Icc a b := by
    rcases le_total (g a) (g b) with h | h
    · simpa only [u, v, min_eq_left h, max_eq_right h] using intermediate_value_Icc hab hg
    · simpa only [u, v, min_eq_right h, max_eq_left h] using intermediate_value_Icc' hab hg
  have hex : ∀ k : ℤ, ∃ x : ℝ, k ∈ A → x ∈ S ∧ g x = (k : ℝ) := by
    intro k
    by_cases hk : k ∈ A
    · have hk' := Finset.mem_Icc.mp hk
      have hkreal : (k : ℝ) ∈ Icc u v := by
        exact ⟨(Int.le_ceil u).trans (by exact_mod_cast hk'.1),
          (show (k : ℝ) ≤ (⌊v⌋ : ℤ) by exact_mod_cast hk'.2).trans (Int.floor_le v)⟩
      obtain ⟨x, hx, he⟩ := hiv hkreal
      exact ⟨x, fun _ => ⟨hlevel x hx k he, he⟩⟩
    · exact ⟨0, fun h => (hk h).elim⟩
  choose F hF using hex
  have hcard : A.card ≤ S.ncard := by
    have h := Set.ncard_le_ncard_of_injOn (s := (A : Set ℤ)) F
      (fun k hk => (hF k hk).1) (by
        intro k hk l hl he
        have hh := congrArg g he
        rw [(hF k hk).2, (hF l hl).2] at hh
        exact_mod_cast hh) hS
    simpa using h
  have hceil := Int.ceil_lt_add_one u
  have hfloor := Int.lt_floor_add_one v
  have horder : ⌈u⌉ ≤ ⌊v⌋ + 1 := by
    by_contra h
    have hi : ⌊v⌋ + 2 ≤ ⌈u⌉ := by omega
    have hr : (⌊v⌋ : ℝ) + 2 ≤ (⌈u⌉ : ℝ) := by exact_mod_cast hi
    linarith
  have hAc : (A.card : ℤ) = ⌊v⌋ + 1 - ⌈u⌉ := Int.card_Icc_of_le _ _ horder
  have hAreal : (A.card : ℝ) = (⌊v⌋ : ℝ) + 1 - (⌈u⌉ : ℝ) := by exact_mod_cast hAc
  have hcardreal : (A.card : ℝ) ≤ (S.ncard : ℝ) := by exact_mod_cast hcard
  have hdiff : |g b - g a| = v - u := by
    rcases le_total (g a) (g b) with h | h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      simp [u, v, min_eq_left h, max_eq_right h]
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]
      simp only [u, v, max_eq_left h, min_eq_right h]
      ring
  rw [hdiff]
  linarith

/-- Net variation of any continuous argument lift. The real-part crossing
condition is supplied by its exact polar representation, not by the branch
of principal argument. -/
theorem continuous_argument_net_change
    (θ : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hθ : ContinuousOn θ (Icc a b))
    (S : Set ℝ) (hS : S.Finite)
    (hcross : ∀ x ∈ Icc a b, Real.cos (θ x) = 0 → x ∈ S) :
    |θ b - θ a| ≤ Real.pi * ((S.ncard : ℝ) + 1) := by
  let g : ℝ → ℝ := fun x => θ x / Real.pi - 1/2
  have hg : ContinuousOn g (Icc a b) := (hθ.div_const _).sub continuousOn_const
  have hl : ∀ x ∈ Icc a b, ∀ k : ℤ, g x = (k : ℝ) → x ∈ S := by
    intro x hx k hk
    apply hcross x hx
    apply Real.cos_eq_zero_iff.mpr
    refine ⟨k, ?_⟩
    change θ x / Real.pi - 1/2 = (k : ℝ) at hk
    have h : θ x / Real.pi = (k : ℝ) + 1/2 := by linarith
    have he := (div_eq_iff Real.pi_ne_zero).mp h
    linarith
  have h := continuous_integer_level_net_change g a b hab hg S hS hl
  have he : g b - g a = (θ b - θ a) / Real.pi := by
    dsimp [g]
    ring
  rw [he, abs_div, abs_of_pos Real.pi_pos] at h
  exact (div_le_iff₀ Real.pi_pos).mp h |>.trans_eq (mul_comm _ _)


end RiemannVonMangoldt
end P2MFinalSource029

/- Source module: UniformLiftArgumentV3
   Original SHA256: 38f557f16640281e8f3a9c5576f1acdea6edebab742683f5dd3aea20173b81e6 -/
section P2MFinalSource030

open Complex Filter Set Metric
open scoped Topology
set_option autoImplicit false

namespace RiemannVonMangoldt

/-- Uniform net argument control for every continuous polar lift on the actual
normalized L-function segment. This does not assert existence of such a lift
or identify it with a log-derivative integral. -/
theorem normalizedHorizontal_lift_argument_uniform :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (hp : χ.IsPrimitive) (t : ℝ), 3 ≤ |t| →
      ∀ θ : ℝ → ℝ, ContinuousOn θ (Icc (-1) 0) →
        (∀ x ∈ Icc (-1 : ℝ) 0,
          normalizedHorizontal χ t (x : ℂ) =
          (‖normalizedHorizontal χ t (x : ℂ)‖ : ℂ) * exp ((θ x : ℂ) * I)) →
        |θ 0 - θ (-1)| ≤ Real.pi *
          (1 + Real.log (1 + (5 * (q : ℝ) * (|t| + 3)) / c) / Real.log (5/4)) := by
  obtain ⟨c, hc, hj⟩ := reflectedHorizontal_distinct_crossings_uniform
  refine ⟨c, hc, ?_⟩
  intro q _ χ hp t ht θ hθ hpolar
  let S := {x : ℝ | x ∈ Icc (-1) 0 ∧ (normalizedHorizontal χ t (x : ℂ)).re = 0}
  have h := hj q χ hp t ht
  have hS : S.Finite := h.1
  have hcS : ∀ x ∈ Icc (-1 : ℝ) 0, Real.cos (θ x) = 0 → x ∈ S := by
    intro x hx hz
    refine ⟨hx, ?_⟩
    rw [hpolar x hx]
    simp [Complex.mul_re, Complex.exp_ofReal_mul_I_re, hz]
  have hv := continuous_argument_net_change θ (-1) 0 (by norm_num) hθ S hS hcS
  have hbound : (S.ncard : ℝ) ≤
      Real.log (1 + (5 * (q : ℝ) * (|t| + 3)) / c) / Real.log (5/4) := h.2
  exact hv.trans (mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le)


end RiemannVonMangoldt
end P2MFinalSource030

/- Source module: IntegratedPolarV2
   Original SHA256: 9ee92f5d93126a9ab3abd3236da7047701f8e8d1f37d422da3686808dbe808e5 -/
section P2MFinalSource031

open Complex Set MeasureTheory Filter
open scoped Topology Interval
set_option autoImplicit false

namespace RiemannVonMangoldt

/-- An actual logarithmic primitive on a zero-free real interval, normalized at 0. -/
theorem exp_integrated_logDeriv (f f' : ℝ → ℂ)
    (hd : ∀ x ∈ Icc (-1 : ℝ) 0, HasDerivAt f (f' x) x)
    (hc : ∀ x ∈ Icc (-1 : ℝ) 0, ContinuousAt f' x)
    (hn : ∀ x ∈ Icc (-1 : ℝ) 0, f x ≠ 0)
    (hm : Measurable (fun x => f' x / f x))
    (h0 : f 0 = 1) :
    ∀ x ∈ Icc (-1 : ℝ) 0, exp (∫ u in 0..x, f' u / f u) = f x := by
  let g : ℝ → ℂ := fun x => f' x / f x
  let G : ℝ → ℂ := fun x => ∫ u in 0..x, g u
  have hg : ∀ x ∈ Icc (-1 : ℝ) 0, ContinuousAt g x :=
    fun x hx => (hc x hx).div (hd x hx).continuousAt (hn x hx)
  have hG : ∀ x ∈ Icc (-1 : ℝ) 0, HasDerivAt G (g x) x := by
    intro x hx
    have hsub : uIcc 0 x ⊆ Icc (-1 : ℝ) 0 := by
      rw [uIcc_of_ge hx.2]
      exact Icc_subset_Icc_left hx.1
    have hgc : ContinuousOn g (Icc (-1 : ℝ) 0) := fun y hy => (hg y hy).continuousWithinAt
    have hi : IntervalIntegrable g volume 0 x := (hgc.mono hsub).intervalIntegrable
    exact intervalIntegral.integral_hasDerivAt_right hi hm.stronglyMeasurable.stronglyMeasurableAtFilter (hg x hx)
  let K : ℝ → ℂ := fun x => f x * exp (-G x)
  have hK : ∀ x ∈ Icc (-1 : ℝ) 0, HasDerivAt K 0 x := by
    intro x hx
    have h := (hd x hx).mul ((hG x hx).neg.cexp)
    convert h using 1 <;> try rfl
    simp only [g]
    field_simp [hn x hx] <;> ring
  intro x hx
  have hsub : uIcc 0 x ⊆ Icc (-1 : ℝ) 0 := by
    rw [uIcc_of_ge hx.2]
    exact Icc_subset_Icc_left hx.1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => hK y (hsub hy))
    (intervalIntegrable_const (c := (0 : ℂ)) (a := 0) (b := x))
  have hk : K x = K 0 := by simpa using (sub_eq_zero.mp (by simpa using h.symm : K x - K 0 = 0))
  have hk0 : K 0 = 1 := by simp [K, G, h0]
  have hh : f x * exp (-G x) = 1 := hk.trans hk0
  have hh' := congrArg (fun z : ℂ => z * exp (G x)) hh
  rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one, one_mul] at hh'
  exact hh'.symm

end RiemannVonMangoldt
end P2MFinalSource031

/- Source module: ActualHorizontalLiftV2
   Original SHA256: 5ce80c7b9bf98c22a0ac3c7d507acf1f4da6307bc0689db88dfda0758a116bd0 -/
section P2MFinalSource032

open Complex Set MeasureTheory Filter
open scoped Topology Interval
set_option autoImplicit false

namespace RiemannVonMangoldt

noncomputable def horizontalLogDeriv {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t x : ℝ) : ℂ :=
  deriv χ.LFunction (horizontalCenter t + (x : ℂ)) /
    χ.LFunction (horizontalCenter t + (x : ℂ))

/-- Actual log-derivative integral constructs the polar lift on a zero-free segment. -/
theorem horizontalLogDeriv_actual_lift {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) (ht : 3 ≤ |t|)
    (hn : ∀ x ∈ Icc (-1 : ℝ) 0, χ.LFunction (horizontalCenter t + (x : ℂ)) ≠ 0) :
    ContinuousOn (fun x : ℝ => (∫ u in 0..x, horizontalLogDeriv χ t u).im) (Icc (-1) 0) ∧
    ∀ x ∈ Icc (-1 : ℝ) 0,
      normalizedHorizontal χ t (x : ℂ) =
      (‖normalizedHorizontal χ t (x : ℂ)‖ : ℂ) *
        exp (((∫ u in 0..x, horizontalLogDeriv χ t u).im : ℝ) * I) := by
  let z : ℝ → ℂ := fun x => horizontalCenter t + (x : ℂ)
  have hz : Continuous z := by dsimp [z]; fun_prop
  have hne : ∀ x : ℝ, z x ≠ 1 := by
    intro x h
    have hi := congrArg Complex.im h
    simp [z, horizontalCenter, Complex.add_im, Complex.mul_im, Complex.div_im] at hi
    have : t = 0 := by linarith
    norm_num [this] at ht
  have ha : AnalyticOnNhd ℂ χ.LFunction ({1}ᶜ : Set ℂ) :=
    (show DifferentiableOn ℂ χ.LFunction ({1}ᶜ : Set ℂ) from
      fun s hs => (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl (by simpa using hs))).differentiableWithinAt).analyticOnNhd isClosed_singleton.isOpen_compl
  have han : ∀ x : ℝ, AnalyticAt ℂ χ.LFunction (z x) :=
    fun x => ha (z x) (by simpa using hne x)
  have hanchor : χ.LFunction (horizontalCenter t) ≠ 0 := by
    simpa using hn 0 (by norm_num)
  let f : ℝ → ℂ := fun x => normalizedHorizontal χ t (x : ℂ)
  let f' : ℝ → ℂ := fun x => deriv χ.LFunction (z x) / χ.LFunction (horizontalCenter t)
  have hd : ∀ x : ℝ, HasDerivAt f (f' x) x := by
    intro x
    have h := ((DirichletCharacter.differentiableAt_LFunction χ (z x) (Or.inl (hne x))).hasDerivAt.comp (x : ℂ)
      ((hasDerivAt_const (x : ℂ) (horizontalCenter t)).add (hasDerivAt_id (x : ℂ)))).div_const (χ.LFunction (horizontalCenter t))
    simpa [f, f', z, normalizedHorizontal] using h.comp_ofReal
  have hc : Continuous f' := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (((han x).deriv.continuousAt.comp (hz.continuousAt : ContinuousAt z x)).div_const _)
  have hnf : ∀ x ∈ Icc (-1 : ℝ) 0, f x ≠ 0 := by
    intro x hx
    exact div_ne_zero (hn x hx) hanchor
  have hf0 : f 0 = 1 := by simp [f, normalizedHorizontal, hanchor]
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hm : Measurable (fun x => f' x / f x) := hc.measurable.div hf.measurable
  have he := exp_integrated_logDeriv f f' (fun x _ => hd x) (fun x _ => hc.continuousAt) hnf hm hf0
  have hratio : (fun x => f' x / f x) = horizontalLogDeriv χ t := by
    funext x
    dsimp [f, f', normalizedHorizontal, horizontalLogDeriv, z]
    rw [div_div_div_cancel_right₀ hanchor]
  rw [hratio] at he hm
  let G : ℝ → ℂ := fun x => ∫ u in 0..x, horizontalLogDeriv χ t u
  have hcont : ∀ x ∈ Icc (-1 : ℝ) 0, ContinuousAt (horizontalLogDeriv χ t) x := by
    intro x hx
    rw [← hratio]
    exact hc.continuousAt.div (hd x).continuousAt (hnf x hx)
  have hG : ContinuousOn G (Icc (-1) 0) := by
    intro x hx
    have hsub : uIcc 0 x ⊆ Icc (-1 : ℝ) 0 := by
      rw [uIcc_of_ge hx.2]
      exact Icc_subset_Icc_left hx.1
    have hgc : ContinuousOn (horizontalLogDeriv χ t) (Icc (-1 : ℝ) 0) :=
      fun y hy => (hcont y hy).continuousWithinAt
    have hi : IntervalIntegrable (horizontalLogDeriv χ t) volume 0 x := (hgc.mono hsub).intervalIntegrable
    exact (intervalIntegral.integral_hasDerivAt_right hi hm.stronglyMeasurable.stronglyMeasurableAtFilter (hcont x hx)).continuousAt.continuousWithinAt
  refine ⟨Complex.continuous_im.comp_continuousOn hG, ?_⟩
  intro x hx
  change f x = (‖f x‖ : ℂ) * exp ((↑(G x).im : ℂ) * I)
  have hex : exp (G x) = f x := he x hx
  rw [← hex, Complex.norm_exp]
  nth_rw 1 [← Complex.re_add_im (G x)]
  rw [Complex.exp_add, Complex.ofReal_exp]


end RiemannVonMangoldt
end P2MFinalSource032

/- Source module: HorizontalIntegralBoundV1
   Original SHA256: a20703e3c51f68bbd2cc2bd30466366a705a26968fdf6b416ecaec4b47167c61 -/
section P2MFinalSource033

open Complex Set MeasureTheory Filter
open scoped Topology Interval
set_option autoImplicit false

namespace RiemannVonMangoldt

/-- Conductor-uniform imaginary log-derivative integral bound at zero-free heights.
No continuous lift is assumed; it is supplied by the actual integral. -/
theorem horizontal_logDeriv_integral_uniform :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (hp : χ.IsPrimitive) (t : ℝ), 3 ≤ |t| →
      (∀ x ∈ Icc (-1 : ℝ) 0, χ.LFunction (horizontalCenter t + (x : ℂ)) ≠ 0) →
      |(∫ x in (-1 : ℝ)..0, horizontalLogDeriv χ t x).im| ≤
        Real.pi * (1 + Real.log (1 + (5 * (q : ℝ) * (|t| + 3)) / c) / Real.log (5/4)) := by
  obtain ⟨c, hc, hb⟩ := normalizedHorizontal_lift_argument_uniform
  refine ⟨c, hc, ?_⟩
  intro q _ χ hp t ht hn
  obtain ⟨hcont, hpolar⟩ := horizontalLogDeriv_actual_lift χ t ht hn
  have h := hb q χ hp t ht (fun x => (∫ u in 0..x, horizontalLogDeriv χ t u).im) hcont hpolar
  simp only [intervalIntegral.integral_same, Complex.zero_im, zero_sub, abs_neg] at h
  rw [intervalIntegral.integral_symm (-1 : ℝ) 0, Complex.neg_im, abs_neg] at h
  exact h

end RiemannVonMangoldt
end P2MFinalSource033

/- Source module: HorizontalUnshiftedV3
   Original SHA256: c35e9f8aed29e8ac8571ba2b82efa2c5765973667e6d3510944218c1c97b2a32 -/
section P2MFinalSource034

open Complex Set MeasureTheory Filter
open scoped Topology Interval
set_option autoImplicit false

namespace RiemannVonMangoldt

/-- The existing centered parametrization is exactly the original horizontal line. -/
lemma horizontalCenter_add_real_eq (t x : ℝ) :
    horizontalCenter t + (x : ℂ) = ((x + 3/2 : ℝ) : ℂ) + (t : ℂ) * I := by
  unfold horizontalCenter
  push_cast
  ring

/-- The actual logarithmic derivative is integrable on the original segment.
Both height signs are included; nonvanishing is only required on the segment. -/
lemma horizontal_logDeriv_intervalIntegrable_original {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) (ht : 3 ≤ |t|)
    (hn : ∀ σ ∈ Icc (1/2 : ℝ) (3/2),
      χ.LFunction ((σ : ℂ) + (t : ℂ) * I) ≠ 0) :
    IntervalIntegrable
      (fun σ : ℝ => logDeriv χ.LFunction ((σ : ℂ) + (t : ℂ) * I))
      volume (1/2 : ℝ) (3/2) := by
  let z : ℝ → ℂ := fun σ => (σ : ℂ) + (t : ℂ) * I
  have hz : Continuous z := by dsimp [z]; fun_prop
  have ht0 : t ≠ 0 := by
    intro h
    norm_num [h] at ht
  have hne : ∀ σ : ℝ, z σ ≠ 1 := by
    intro σ h
    apply ht0
    simpa [z, Complex.add_im, Complex.mul_im] using congrArg Complex.im h
  have ha : AnalyticOnNhd ℂ χ.LFunction ({1}ᶜ : Set ℂ) :=
    (show DifferentiableOn ℂ χ.LFunction ({1}ᶜ : Set ℂ) from
      fun s hs => (DirichletCharacter.differentiableAt_LFunction χ s
        (Or.inl (by simpa using hs))).differentiableWithinAt).analyticOnNhd
          isClosed_singleton.isOpen_compl
  have han : ∀ σ : ℝ, AnalyticAt ℂ χ.LFunction (z σ) :=
    fun σ => ha (z σ) (by simpa using hne σ)
  have hc : ContinuousOn
      (fun σ : ℝ => logDeriv χ.LFunction (z σ))
      (uIcc (1/2 : ℝ) (3/2)) := by
    rw [uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 3/2)]
    intro σ hσ
    have hD : ContinuousAt (fun x : ℝ => deriv χ.LFunction (z x)) σ :=
      (han σ).deriv.continuousAt.comp
        (hz.continuousAt : ContinuousAt z σ)
    have hL : ContinuousAt (fun x : ℝ => χ.LFunction (z x)) σ :=
      (han σ).continuousAt.comp
        (hz.continuousAt : ContinuousAt z σ)
    have hquot : ContinuousAt
        (fun x : ℝ => deriv χ.LFunction (z x) / χ.LFunction (z x)) σ :=
      hD.div hL (hn σ hσ)
    simpa only [logDeriv_apply] using hquot.continuousWithinAt
  exact hc.intervalIntegrable

/-- Translation preserves the exact orientation and endpoints of the integral. -/
lemma horizontal_logDeriv_integral_unshift {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (∫ x in (-1 : ℝ)..0, horizontalLogDeriv χ t x) =
      ∫ σ in (1/2 : ℝ)..(3/2),
        logDeriv χ.LFunction ((σ : ℂ) + (t : ℂ) * I) := by
  let f : ℝ → ℂ := fun σ => logDeriv χ.LFunction ((σ : ℂ) + (t : ℂ) * I)
  have hf : horizontalLogDeriv χ t = fun x : ℝ => f (x + 3/2) := by
    funext x
    change deriv χ.LFunction (horizontalCenter t + (x : ℂ)) /
        χ.LFunction (horizontalCenter t + (x : ℂ)) =
      logDeriv χ.LFunction (((x + 3/2 : ℝ) : ℂ) + (t : ℂ) * I)
    rw [horizontalCenter_add_real_eq, logDeriv_apply]
  rw [hf]
  have h := intervalIntegral.integral_comp_add_right
    (a := (-1 : ℝ)) (b := (0 : ℝ)) f (3/2 : ℝ)
  simpa only [show (-1 : ℝ) + 3/2 = 1/2 by norm_num, zero_add, f] using h

/-- The original horizontal imaginary logarithmic-derivative integral has the
same conductor-uniform estimate. Integrability and commuting imaginary part
with integration are supplied, not assumed. -/
theorem horizontal_logDeriv_integral_uniform_unshifted :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (hp : χ.IsPrimitive) (t : ℝ), 3 ≤ |t| →
      (∀ σ ∈ Icc (1/2 : ℝ) (3/2),
        χ.LFunction ((σ : ℂ) + (t : ℂ) * I) ≠ 0) →
      IntervalIntegrable
        (fun σ : ℝ => logDeriv χ.LFunction ((σ : ℂ) + (t : ℂ) * I))
        volume (1/2 : ℝ) (3/2) ∧
      (∫ σ in (1/2 : ℝ)..(3/2),
        (logDeriv χ.LFunction ((σ : ℂ) + (t : ℂ) * I)).im) =
        (∫ σ in (1/2 : ℝ)..(3/2),
          logDeriv χ.LFunction ((σ : ℂ) + (t : ℂ) * I)).im ∧
      |∫ σ in (1/2 : ℝ)..(3/2),
        (logDeriv χ.LFunction ((σ : ℂ) + (t : ℂ) * I)).im| ≤
        Real.pi * (1 + Real.log (1 + (5 * (q : ℝ) * (|t| + 3)) / c) /
          Real.log (5/4)) := by
  obtain ⟨c, hc, hb⟩ := horizontal_logDeriv_integral_uniform
  refine ⟨c, hc, ?_⟩
  intro q _ χ hp t ht hn
  have hi := horizontal_logDeriv_intervalIntegrable_original χ t ht hn
  have him : (∫ σ in (1/2 : ℝ)..(3/2),
      (logDeriv χ.LFunction ((σ : ℂ) + (t : ℂ) * I)).im) =
      (∫ σ in (1/2 : ℝ)..(3/2),
        logDeriv χ.LFunction ((σ : ℂ) + (t : ℂ) * I)).im := by
    simpa using intervalIntegral.intervalIntegral_im hi
  refine ⟨hi, him, ?_⟩
  rw [him]
  have hn' : ∀ x ∈ Icc (-1 : ℝ) 0,
      χ.LFunction (horizontalCenter t + (x : ℂ)) ≠ 0 := by
    intro x hx
    have hx' : x + 3/2 ∈ Icc (1/2 : ℝ) (3/2) := by
      constructor <;> linarith [hx.1, hx.2]
    rw [horizontalCenter_add_real_eq]
    exact hn (x + 3/2) hx'
  have h := hb q χ hp t ht hn'
  rw [horizontal_logDeriv_integral_unshift] at h
  exact h

/-- For a fixed positive anchor, the explicit Jensen expression is bounded by
an absolute multiple of log(Q*u), uniformly for Q >= 1 and u >= 3. -/
lemma horizontal_jensen_bound_absorb (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q u : ℝ), 1 ≤ Q → 3 ≤ u →
      Real.pi * (1 + Real.log (1 + (5 * Q * (u + 3)) / c) / Real.log (5/4)) ≤
        C * Real.log (Q * u) := by
  let A : ℝ := 1 + 10/c
  let d : ℝ := Real.log (5/4)
  let l : ℝ := Real.log 3
  let K : ℝ := 1 + Real.log A / d
  let C : ℝ := Real.pi * (K/l + 1/d)
  have hA1 : 1 ≤ A := by
    have h : 0 ≤ 10/c := by positivity
    dsimp [A]
    linarith
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hd : 0 < d := Real.log_pos (by norm_num : (1 : ℝ) < 5/4)
  have hl : 0 < l := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA1
  have hK : 0 < K := by dsimp [K]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Q u hQ hu
  have hQ0 : 0 ≤ Q := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hxu : u ≤ Q*u := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hQ hu0
  have hx3 : 3 ≤ Q*u := hu.trans hxu
  have hx : 0 < Q*u := by linarith
  have hx1 : 1 ≤ Q*u := by linarith
  have hu2 : u + 3 ≤ 2*u := by linarith
  have harg : 1 + (5*Q*(u+3))/c ≤ A*(Q*u) := by
    calc
      _ ≤ 1 + (5*Q*(2*u))/c := add_le_add (le_refl (1 : ℝ))
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hu2 (by positivity : 0 ≤ 5*Q)) hc.le)
      _ = 1 + (10/c)*(Q*u) := by ring
      _ ≤ Q*u + (10/c)*(Q*u) := add_le_add hx1 (le_refl ((10/c)*(Q*u)))
      _ = A*(Q*u) := by dsimp [A]; ring
  have hlog : Real.log (1 + (5*Q*(u+3))/c) ≤ Real.log A + Real.log (Q*u) := by
    calc
      _ ≤ Real.log (A*(Q*u)) := Real.log_le_log (by positivity) harg
      _ = _ := Real.log_mul (ne_of_gt hA) (ne_of_gt hx)
  have hxl : l ≤ Real.log (Q*u) := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hx3
  have hbig : 1 + Real.log (1 + (5*Q*(u+3))/c)/d ≤ K + Real.log (Q*u)/d := by
    calc
      _ ≤ 1 + (Real.log A + Real.log (Q*u))/d :=
        add_le_add (le_refl (1 : ℝ)) (div_le_div_of_nonneg_right hlog hd.le)
      _ = _ := by dsimp [K]; ring
  have hKbound : K ≤ (K/l)*Real.log (Q*u) := by
    have h := mul_le_mul_of_nonneg_left hxl (by positivity : 0 ≤ K/l)
    have hcancel : (K/l)*l = K := by field_simp [ne_of_gt hl]
    rwa [hcancel] at h
  change Real.pi * (1 + Real.log (1 + (5*Q*(u+3))/c)/d) ≤ C * Real.log (Q*u)
  calc
    _ ≤ Real.pi * (K + Real.log (Q*u)/d) :=
      mul_le_mul_of_nonneg_left hbig Real.pi_pos.le
    _ ≤ Real.pi * ((K/l)*Real.log (Q*u) + Real.log (Q*u)/d) :=
      mul_le_mul_of_nonneg_left (add_le_add hKbound (le_refl (Real.log (Q*u)/d))) Real.pi_pos.le
    _ = C * Real.log (Q*u) := by dsimp [C]; ring

/-- Uniform O(log(q*abs(t))) control for the actual horizontal argument integral,
with one constant quantified before the conductor, character and signed height. -/
theorem horizontal_argument_integral_log_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (hp : χ.IsPrimitive) (t : ℝ), 3 ≤ |t| →
      (∀ σ ∈ Icc (1/2 : ℝ) (3/2),
        χ.LFunction ((σ : ℂ) + (t : ℂ) * I) ≠ 0) →
      IntervalIntegrable
        (fun σ : ℝ => logDeriv χ.LFunction ((σ : ℂ) + (t : ℂ) * I))
        volume (1/2 : ℝ) (3/2) ∧
      (∫ σ in (1/2 : ℝ)..(3/2),
        (logDeriv χ.LFunction ((σ : ℂ) + (t : ℂ) * I)).im) =
        (∫ σ in (1/2 : ℝ)..(3/2),
          logDeriv χ.LFunction ((σ : ℂ) + (t : ℂ) * I)).im ∧
      |∫ σ in (1/2 : ℝ)..(3/2),
        (logDeriv χ.LFunction ((σ : ℂ) + (t : ℂ) * I)).im| ≤
        C * Real.log ((q : ℝ) * |t|) := by
  obtain ⟨c, hc, hb⟩ := horizontal_logDeriv_integral_uniform_unshifted
  obtain ⟨C, hC, hbound⟩ := horizontal_jensen_bound_absorb c hc
  refine ⟨C, hC, ?_⟩
  intro q _ χ hp t ht hn
  obtain ⟨hi, him, h⟩ := hb q χ hp t ht hn
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  exact ⟨hi, him, h.trans (hbound (q : ℝ) |t| hq ht)⟩


end RiemannVonMangoldt
end P2MFinalSource034

/- Source module: RightVerticalPrimitiveV3
   Original SHA256: 754620ba69d58cbe65bc6b307e5c1e10298f0bc9bf79727d5f8537bf36b0b902 -/
section P2MFinalSource035

open Complex Set MeasureTheory Filter
open scoped Topology
set_option autoImplicit false

namespace RiemannVonMangoldt

/-- The classical logarithmic Dirichlet-series coefficients. This definition
does not identify the primitive with a chosen principal logarithm. -/
noncomputable def rightLogCoeff {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  χ n * ((ArithmeticFunction.vonMangoldt n / Real.log n : ℝ) : ℂ)

lemma rightLogCoeff_norm_le_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n : ℕ) : ‖rightLogCoeff χ n‖ ≤ 1 := by
  by_cases h0 : n = 0
  · subst n; simp [rightLogCoeff]
  by_cases h1 : n = 1
  · subst n; simp [rightLogCoeff]
  have hn : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hl : 0 < Real.log n := Real.log_pos hn
  have hw0 : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.log n :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg hl.le
  have hw1 : ArithmeticFunction.vonMangoldt n / Real.log n ≤ 1 :=
    (div_le_one hl).mpr ArithmeticFunction.vonMangoldt_le_log
  rw [rightLogCoeff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0]
  exact mul_le_one₀ (χ.norm_le_one n) hw0 hw1

lemma logMul_rightLogCoeff {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    LSeries.logMul (rightLogCoeff χ) =
      (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) := by
  funext n
  by_cases h0 : n = 0
  · subst n; simp [LSeries.logMul, rightLogCoeff]
  by_cases h1 : n = 1
  · subst n; simp [LSeries.logMul, rightLogCoeff]
  have hn : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hl : Real.log n ≠ 0 := ne_of_gt (Real.log_pos hn)
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    simpa using (Complex.ofReal_log (show (0 : ℝ) ≤ n by positivity)).symm
  simp only [LSeries.logMul, rightLogCoeff, hlog, Complex.ofReal_div]
  have hlc : (Real.log n : ℂ) ≠ 0 := by exact_mod_cast hl
  field_simp [hlc] <;> ring

noncomputable def rightLogPrimitive {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : ℂ → ℂ := LSeries (rightLogCoeff χ)

theorem rightLogPrimitive_hasDerivAt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 1 < s.re) :
    HasDerivAt (rightLogPrimitive χ) (logDeriv χ.LFunction s) s := by
  have hab : LSeries.abscissaOfAbsConv (rightLogCoeff χ) ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => rightLogCoeff_norm_le_one χ n⟩
  have hlt : LSeries.abscissaOfAbsConv (rightLogCoeff χ) < s.re :=
    hab.trans_lt (by exact_mod_cast hs)
  have hd := LSeries_hasDerivAt hlt
  rw [logMul_rightLogCoeff χ] at hd
  have hec : ((fun n : ℕ => χ n) * (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))) =
      (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) := by ext n; rfl
  have hid := χ.LSeries_twist_vonMangoldt_eq hs
  rw [← χ.deriv_LFunction_eq_deriv_LSeries hs, ← χ.LFunction_eq_LSeries hs] at hid
  simp only [hec] at hid
  simpa only [rightLogPrimitive, hid, neg_div, neg_neg, logDeriv_apply] using hd

theorem rightLogPrimitive_norm_uniform :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (s : ℂ), s.re = 3/2 → ‖rightLogPrimitive χ s‖ ≤ A := by
  let z : ℂ := ((3/2 : ℝ) : ℂ)
  let A : ℝ := ∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) z n‖
  have hz : 1 < z.re := by norm_num [z]
  have hone : LSeriesSummable (1 : ℕ → ℂ) z := LSeriesSummable_one_iff.mpr hz
  refine ⟨A, tsum_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro q _ χ s hs
  have hs1 : 1 < s.re := by linarith
  have hsum : LSeriesSummable (rightLogCoeff χ) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => rightLogCoeff_norm_le_one χ n) hs1
  have hterm (n : ℕ) : ‖LSeries.term (rightLogCoeff χ) s n‖ ≤
      ‖LSeries.term (1 : ℕ → ℂ) z n‖ := by
    calc
      _ ≤ ‖LSeries.term (1 : ℕ → ℂ) s n‖ := by
        apply LSeries.norm_term_le
        simpa using rightLogCoeff_norm_le_one χ n
      _ ≤ _ := LSeries.norm_term_le_of_re_le_re _ (by norm_num [z, hs]) n
  calc
    ‖rightLogPrimitive χ s‖ ≤ ∑' n : ℕ, ‖LSeries.term (rightLogCoeff χ) s n‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ A := Summable.tsum_le_tsum hterm hsum.norm hone.norm

/-- The actual vertical logarithmic-derivative integral is uniformly bounded
for arbitrary endpoints and every Dirichlet character, including modulus one. -/
theorem right_vertical_logDeriv_integral_uniform :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (a b : ℝ),
      IntervalIntegrable (fun t : ℝ => I * logDeriv χ.LFunction (3/2 + (t : ℂ)*I))
        volume a b ∧
      ‖∫ t in a..b, I * logDeriv χ.LFunction (3/2 + (t : ℂ)*I)‖ ≤ K := by
  obtain ⟨A, hA, hB⟩ := rightLogPrimitive_norm_uniform
  refine ⟨2*A, by positivity, ?_⟩
  intro q _ χ a b
  let z : ℝ → ℂ := fun t => 3/2 + (t : ℂ)*I
  have hzre (t : ℝ) : (z t).re = 3/2 := by simp [z]
  have hzne (t : ℝ) : z t ≠ 1 := by
    intro h; have h' := congrArg Complex.re h; rw [hzre] at h'; norm_num at h'
  have hLne (t : ℝ) : χ.LFunction (z t) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inr (hzne t)) (by rw [hzre]; norm_num)
  have hz : Continuous z := by dsimp [z]; fun_prop
  have ha : AnalyticOnNhd ℂ χ.LFunction ({1}ᶜ : Set ℂ) :=
    (show DifferentiableOn ℂ χ.LFunction ({1}ᶜ : Set ℂ) from
      fun s hs => (DirichletCharacter.differentiableAt_LFunction χ s
        (Or.inl (by simpa using hs))).differentiableWithinAt).analyticOnNhd
          isClosed_singleton.isOpen_compl
  have hg : Continuous (fun t : ℝ => I * logDeriv χ.LFunction (z t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have han : AnalyticAt ℂ χ.LFunction (z t) := ha (z t) (by simpa using hzne t)
    have hD : ContinuousAt (fun u : ℝ => deriv χ.LFunction (z u)) t :=
      han.deriv.continuousAt.comp (hz.continuousAt : ContinuousAt z t)
    have hL : ContinuousAt (fun u : ℝ => χ.LFunction (z u)) t :=
      han.continuousAt.comp (hz.continuousAt : ContinuousAt z t)
    have hquot : ContinuousAt
        (fun u : ℝ => deriv χ.LFunction (z u) / χ.LFunction (z u)) t :=
      hD.div hL (hLne t)
    simpa only [logDeriv_apply] using hquot.const_mul I
  have hd (t : ℝ) : HasDerivAt (fun u : ℝ => rightLogPrimitive χ (z u))
      (I * logDeriv χ.LFunction (z t)) t := by
    have h := (rightLogPrimitive_hasDerivAt χ (z t) (by rw [hzre]; norm_num)).comp (t : ℂ)
      ((hasDerivAt_const (t : ℂ) (3/2 : ℂ)).add ((hasDerivAt_id (t : ℂ)).mul_const I))
    simpa [z, Function.comp_def, mul_comm] using h.comp_ofReal
  have hi : IntervalIntegrable (fun t : ℝ => I * logDeriv χ.LFunction (z t)) volume a b :=
    hg.intervalIntegrable a b
  refine ⟨hi, ?_⟩
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  change ‖∫ t in a..b, I * logDeriv χ.LFunction (z t)‖ ≤ 2*A
  rw [he]
  calc
    ‖rightLogPrimitive χ (z b) - rightLogPrimitive χ (z a)‖ ≤
        ‖rightLogPrimitive χ (z b)‖ + ‖rightLogPrimitive χ (z a)‖ := norm_sub_le _ _
    _ ≤ A + A := add_le_add (hB q χ (z b) (hzre b)) (hB q χ (z a) (hzre a))
    _ = 2*A := by ring

end RiemannVonMangoldt
end P2MFinalSource035

/- Source module: LContourErrorV3
   Original SHA256: 3d50616134887203132c9347d1ef30bd32f94351066477b126e35c9d31ebfa56 -/
section P2MFinalSource036

/-!
Aggregate the two already-checked original-L edge estimates on the exact
paired contour terms. The constant is chosen before the conductor,
character and height. Only the actual four signed good-height conditions
are retained, with the inverse character explicitly present.
-/

set_option autoImplicit false

open Complex Set MeasureTheory
open scoped Interval

namespace RiemannVonMangoldt.Contour

private lemma abs_four_terms (a b c d : ℝ) :
    |a + b - c - d| ≤ |a| + |b| + |c| + |d| := by
  calc
    |a + b - c - d| ≤ |a + b - c| + |d| := abs_sub _ _
    _ ≤ (|a + b| + |c|) + |d| := add_le_add (abs_sub _ _) (le_refl _)
    _ ≤ (|a| + |b| + |c|) + |d| :=
      add_le_add (add_le_add (abs_add_le _ _) (le_refl _)) (le_refl _)
    _ = _ := by ring

/-- Uniform control of all six original-L contour terms by one absolute
multiple of log(q*T). The right-edge estimate uses the genuine bounded
Dirichlet-series primitive, and the horizontal estimates bound actual net
argument integrals rather than integrals of their absolute values. -/
theorem paired_L_contour_error_log_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
      (hp : chi.IsPrimitive) (T : ℝ), 3 ≤ T →
      (∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2),
        chi.LFunction ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      (∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2),
        chi.LFunction ((x : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0) →
      (∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2),
        (chi⁻¹).LFunction ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      (∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2),
        (chi⁻¹).LFunction ((x : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0) →
      |((rightVertical (logDeriv chi.LFunction) T).re +
          (rightVertical (logDeriv (chi⁻¹).LFunction) T).re) +
        ((horizontal (logDeriv chi.LFunction) (-T)).im +
          (horizontal (logDeriv (chi⁻¹).LFunction) (-T)).im -
          (horizontal (logDeriv chi.LFunction) T).im -
          (horizontal (logDeriv (chi⁻¹).LFunction) T).im)| ≤
        C * Real.log ((q : ℝ) * T) := by
  obtain ⟨CH, hCH, hH⟩ := horizontal_argument_integral_log_uniform
  obtain ⟨K, hK, hV⟩ := right_vertical_logDeriv_integral_uniform
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  refine ⟨4 * CH + 2 * K / Real.log 3, by positivity, ?_⟩
  intro q _ chi hp T hT hchipos hchineg hipos hineg
  have hT0 : 0 ≤ T := by linarith
  have hTabs : 3 ≤ |T| := by simpa only [abs_of_nonneg hT0] using hT
  have hTnegabs : 3 ≤ |-T| := by simpa only [abs_neg] using hTabs
  have hpi : (chi⁻¹).IsPrimitive := by
    change (chi⁻¹).conductor = q
    rw [DirichletCharacter.conductor_inv]
    exact hp
  have hhpos : |(horizontal (logDeriv chi.LFunction) T).im| ≤
      CH * Real.log ((q : ℝ) * T) := by
    obtain ⟨_, him, hb⟩ := hH q chi hp T hTabs hchipos
    rw [him] at hb
    simpa only [horizontal, abs_of_nonneg hT0] using hb
  have hhneg : |(horizontal (logDeriv chi.LFunction) (-T)).im| ≤
      CH * Real.log ((q : ℝ) * T) := by
    obtain ⟨_, him, hb⟩ := hH q chi hp (-T) hTnegabs hchineg
    rw [him] at hb
    simpa only [horizontal, abs_neg, abs_of_nonneg hT0] using hb
  have hhipos : |(horizontal (logDeriv (chi⁻¹).LFunction) T).im| ≤
      CH * Real.log ((q : ℝ) * T) := by
    obtain ⟨_, him, hb⟩ := hH q (chi⁻¹) hpi T hTabs hipos
    rw [him] at hb
    simpa only [horizontal, abs_of_nonneg hT0] using hb
  have hhineg : |(horizontal (logDeriv (chi⁻¹).LFunction) (-T)).im| ≤
      CH * Real.log ((q : ℝ) * T) := by
    obtain ⟨_, him, hb⟩ := hH q (chi⁻¹) hpi (-T) hTnegabs hineg
    rw [him] at hb
    simpa only [horizontal, abs_neg, abs_of_nonneg hT0] using hb
  have hv : |(rightVertical (logDeriv chi.LFunction) T).re| ≤ K := by
    have hn : ‖rightVertical (logDeriv chi.LFunction) T‖ ≤ K := by
      simpa [rightVertical, intervalIntegral.integral_const_mul, norm_mul] using
        (hV q chi (-T) T).2
    exact (Complex.abs_re_le_norm _).trans hn
  have hiv : |(rightVertical (logDeriv (chi⁻¹).LFunction) T).re| ≤ K := by
    have hn : ‖rightVertical (logDeriv (chi⁻¹).LFunction) T‖ ≤ K := by
      simpa [rightVertical, intervalIntegral.integral_const_mul, norm_mul] using
        (hV q (chi⁻¹) (-T) T).2
    exact (Complex.abs_re_le_norm _).trans hn
  have hhorizontal :
      |(horizontal (logDeriv chi.LFunction) (-T)).im +
        (horizontal (logDeriv (chi⁻¹).LFunction) (-T)).im -
        (horizontal (logDeriv chi.LFunction) T).im -
        (horizontal (logDeriv (chi⁻¹).LFunction) T).im| ≤
      4 * CH * Real.log ((q : ℝ) * T) := by
    calc
      _ ≤ |(horizontal (logDeriv chi.LFunction) (-T)).im| +
          |(horizontal (logDeriv (chi⁻¹).LFunction) (-T)).im| +
          |(horizontal (logDeriv chi.LFunction) T).im| +
          |(horizontal (logDeriv (chi⁻¹).LFunction) T).im| := abs_four_terms _ _ _ _
      _ ≤ CH * Real.log ((q : ℝ) * T) + CH * Real.log ((q : ℝ) * T) +
          CH * Real.log ((q : ℝ) * T) + CH * Real.log ((q : ℝ) * T) :=
        add_le_add (add_le_add (add_le_add hhneg hhineg) hhpos) hhipos
      _ = _ := by ring
  have hvertical :
      |(rightVertical (logDeriv chi.LFunction) T).re +
        (rightVertical (logDeriv (chi⁻¹).LFunction) T).re| ≤ 2 * K := by
    calc
      _ ≤ |(rightVertical (logDeriv chi.LFunction) T).re| +
          |(rightVertical (logDeriv (chi⁻¹).LFunction) T).re| := abs_add_le _ _
      _ ≤ K + K := add_le_add hv hiv
      _ = _ := by ring
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqt : 3 ≤ (q : ℝ) * T := by
    have h := mul_le_mul_of_nonneg_right hq hT0
    simp only [one_mul] at h
    exact hT.trans h
  have hl : Real.log 3 ≤ Real.log ((q : ℝ) * T) :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 3) hqt
  have hkabsorb : 2 * K ≤ (2 * K / Real.log 3) * Real.log ((q : ℝ) * T) := by
    calc
      2 * K = (2 * K / Real.log 3) * Real.log 3 := by field_simp [ne_of_gt hl3]
      _ ≤ (2 * K / Real.log 3) * Real.log ((q : ℝ) * T) :=
        mul_le_mul_of_nonneg_left hl (by positivity)
  calc
    _ ≤ |(rightVertical (logDeriv chi.LFunction) T).re +
          (rightVertical (logDeriv (chi⁻¹).LFunction) T).re| +
        |(horizontal (logDeriv chi.LFunction) (-T)).im +
          (horizontal (logDeriv (chi⁻¹).LFunction) (-T)).im -
          (horizontal (logDeriv chi.LFunction) T).im -
          (horizontal (logDeriv (chi⁻¹).LFunction) T).im| := abs_add_le _ _
    _ ≤ 2 * K + 4 * CH * Real.log ((q : ℝ) * T) :=
      add_le_add hvertical hhorizontal
    _ ≤ (2 * K / Real.log 3) * Real.log ((q : ℝ) * T) +
        4 * CH * Real.log ((q : ℝ) * T) := add_le_add hkabsorb (le_refl _)
    _ = (4 * CH + 2 * K / Real.log 3) * Real.log ((q : ℝ) * T) := by ring

end RiemannVonMangoldt.Contour

end P2MFinalSource036

/- Source module: UnitIntervalLogIntegralV2
   Original SHA256: 73a6482a134f054efc23ab77bfcafca27f1ba97e214307c83a19451d76d99436 -/
section P2MFinalSource037

-- The exact principal-log integral identity, preserving both endpoints.
set_option autoImplicit false

namespace RiemannVonMangoldt

/-- The right-half-plane complex logarithm is an antiderivative of the
reciprocal along horizontal segments. The nonzero imaginary part makes the
reciprocal continuous on the entire real parameter line. -/
theorem reciprocal_interval_integral_log
    (z : ℂ) (hz : 0 < z.re) (ht : z.im ≠ 0)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, (z + (t : ℂ))⁻¹) =
      Complex.log (z + (b : ℂ)) - Complex.log (z + (a : ℂ)) := by
  have hne : ∀ t : ℝ, z + (t : ℂ) ≠ 0 := by
    intro t h
    have hh := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, add_zero, Complex.zero_im] at hh
    exact ht hh
  have hderiv (t : ℝ) (ht0 : 0 ≤ t) :
      HasDerivAt (fun s : ℝ => Complex.log (z + (s : ℂ)))
        ((z + (t : ℂ))⁻¹) t := by
    have hs : z + (t : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith
    have hlin : HasDerivAt (fun s : ℝ => z + (s : ℂ)) (1 : ℂ) t := by
      convert ((hasDerivAt_id (t : ℂ)).const_add z).comp_ofReal using 1 <;> simp
    convert hlin.clog_real hs using 1 <;> simp
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t htab
    rw [Set.uIcc_of_le hab] at htab
    exact hderiv t (le_trans ha htab.1)
  · exact (Continuous.inv₀ (by fun_prop) hne).intervalIntegrable _ _


/-- Summing all `n+1` unit reciprocal integrals gives precisely the principal
complex logarithm increment to the endpoint `n+1`. -/
theorem reciprocal_sum_interval_integral_log
    (z : ℂ) (hz : 0 < z.re) (ht : z.im ≠ 0) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
      ∫ t in (j : ℝ)..((j + 1 : ℕ) : ℝ), (z + (t : ℂ))⁻¹) =
        Complex.log (z + ((n + 1 : ℕ) : ℂ)) - Complex.log z := by
  calc
    _ = ∑ j ∈ Finset.range (n + 1),
          (Complex.log (z + ((j + 1 : ℕ) : ℂ)) -
           Complex.log (z + (j : ℂ))) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact reciprocal_interval_integral_log z hz ht (j : ℝ)
        ((j + 1 : ℕ) : ℝ) (Nat.cast_nonneg _)
          (by exact_mod_cast (Nat.le_succ j))
    _ = Complex.log (z + ((n + 1 : ℕ) : ℂ)) - Complex.log z := by
      simpa using (Finset.sum_range_sub
        (fun j : ℕ => Complex.log (z + (j : ℂ))) (n + 1))

end RiemannVonMangoldt
end P2MFinalSource037

/- Source module: ReciprocalIntervalErrorV2
   Original SHA256: 2d3a2c499cc0b149211fe27a70776095d2da03848fdfc90ef19f0034000e530b -/
section P2MFinalSource038

set_option autoImplicit false
namespace RiemannVonMangoldt

/-- Rightward real translation cannot decrease a norm in the right half-plane. -/
private theorem norm_le_norm_add_nonneg_real
    (w : ℂ) (u : ℝ) (hw : 0 ≤ w.re) (hu : 0 ≤ u) :
    ‖w‖ ≤ ‖w + (u : ℂ)‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, add_zero]
  nlinarith [mul_nonneg hw hu, sq_nonneg u]

/-- Pointwise horizontal unit-step reciprocal discrepancy, with exact
real quadratic denominator and no height-sign restriction. -/
theorem reciprocal_horizontal_interval_error
    (w : ℂ) (hw : 0 < w.re) (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖w⁻¹ - (w + (u : ℂ))⁻¹‖ ≤ 1 / (w.re ^ 2 + w.im ^ 2) := by
  have hwne : w ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.zero_re] at h'
    linarith
  have hwune : w + (u : ℂ) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at h'
    linarith
  have hmono : ‖w‖ ≤ ‖w + (u : ℂ)‖ :=
    norm_le_norm_add_nonneg_real w u (le_of_lt hw) hu
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  have hupos : 0 < ‖w + (u : ℂ)‖ := norm_pos_iff.mpr hwune
  have hsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using (Complex.normSq_eq_norm_sq w).symm
  have hident : w⁻¹ - (w + (u : ℂ))⁻¹ = (u : ℂ) / (w * (w + (u : ℂ))) := by
    field_simp [hwne, hwune]
    ring
  rw [hident, norm_div, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
  rw [← hsq]
  have hden : 0 < ‖w‖ * ‖w + (u : ℂ)‖ := mul_pos hpos hupos
  have hsqp : 0 < ‖w‖ ^ 2 := sq_pos_of_pos hpos
  apply (div_le_div_iff₀ hden hsqp).2
  nlinarith [mul_le_mul_of_nonneg_left hmono (le_of_lt hpos),
    mul_le_mul_of_nonneg_right hu1 (sq_nonneg ‖w‖)]

end RiemannVonMangoldt
end P2MFinalSource038

/- Source module: UnitIntervalIntegralBoundV2
   Original SHA256: 121fb4527e0105bdfdbb61777a3a666f72fa9dfa5c7f4765524cd138540d7231 -/
section P2MFinalSource039

set_option autoImplicit false
namespace RiemannVonMangoldt

/-- A continuous reciprocal on the real horizontal line when the imaginary part
is nonzero. -/
theorem reciprocal_unit_integral_error
    (w : ℂ) (hw : 0 < w.re) (hi : w.im ≠ 0) :
    ‖w⁻¹ - (∫ u in (0 : ℝ)..1, (w + (u : ℂ))⁻¹)‖ ≤
      1 / (w.re ^ 2 + w.im ^ 2) := by
  have hne : ∀ u : ℝ, w + (u : ℂ) ≠ 0 := by
    intro u h
    have h' := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, add_zero, Complex.zero_im] at h'
    exact hi h'
  have hcont : Continuous (fun u : ℝ => (w + (u : ℂ))⁻¹) :=
    Continuous.inv₀ (by fun_prop) hne
  have hint : IntervalIntegrable (fun u : ℝ => (w + (u : ℂ))⁻¹)
      MeasureTheory.volume (0 : ℝ) 1 := hcont.intervalIntegrable _ _
  calc
    ‖w⁻¹ - (∫ u in (0 : ℝ)..1, (w + (u : ℂ))⁻¹)‖ =
        ‖∫ u in (0 : ℝ)..1, w⁻¹ - (w + (u : ℂ))⁻¹‖ := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hint]
      simp
    _ ≤ (1 / (w.re ^ 2 + w.im ^ 2)) * |(1 : ℝ) - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro u hu
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
      exact reciprocal_horizontal_interval_error w hw u (le_of_lt hu.1) hu.2
    _ = 1 / (w.re ^ 2 + w.im ^ 2) := by norm_num

end RiemannVonMangoldt
end P2MFinalSource039

/- Source module: FiniteQuadraticShiftV2
   Original SHA256: 8ba4f21fd6c12cb1e7955d049114365eb515c0480c4c6522007cf92042a56eab -/
section P2MFinalSource040

-- Independent proof unit for the exact finite majorant; complete parent remains unfinished.

set_option autoImplicit false

namespace RiemannVonMangoldt

-- For j >= 1, compare a quadratic reciprocal with a telescoping rational term.
-- The difference in denominators is a sum of a square and positive terms.
private theorem reciprocal_quadratic_step (a : ℝ) (ha : 1 ≤ a) (n : ℕ) :
    (1 : ℝ) / (((n : ℝ) + 1) ^ 2 + a ^ 2) ≤
      2 / (a + (n : ℝ)) - 2 / (a + (n : ℝ) + 1) := by
  have ha0 : 0 < a := by linarith
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hp : 0 < a + (n : ℝ) := by linarith
  have hq : 0 < a + (n : ℝ) + 1 := by linarith
  have hd : 0 < ((n : ℝ) + 1) ^ 2 + a ^ 2 := by positivity
  have htel : 2 / (a + (n : ℝ)) - 2 / (a + (n : ℝ) + 1) =
      2 / ((a + (n : ℝ)) * (a + (n : ℝ) + 1)) := by
    field_simp
    ring
  rw [htel]
  apply (div_le_div_iff₀ hd (mul_pos hp hq)).2
  nlinarith [sq_nonneg ((n : ℝ) + 1 - a)]

/-- A finite quadratic reciprocal bound, valid uniformly for `a ≥ 1`.
The proof avoids a continuum integral: all terms after `j=0` are bounded
by a rational telescoping difference, preserving the exact `n+1` endpoint. -/
theorem reciprocal_quadratic_range_bound (a : ℝ) (ha : 1 ≤ a) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (1 : ℝ) / ((j : ℝ) ^ 2 + a ^ 2)) ≤ 3 / a := by
  have hprefix : ∀ k : ℕ,
      (∑ j ∈ Finset.range (k + 1), (1 : ℝ) / ((j : ℝ) ^ 2 + a ^ 2)) ≤
        1 / a ^ 2 + 2 / a - 2 / (a + (k : ℝ)) := by
    intro k
    induction k with
    | zero =>
      simp
    | succ k ih =>
      calc
        (∑ j ∈ Finset.range (Nat.succ k + 1),
             (1 : ℝ) / ((j : ℝ) ^ 2 + a ^ 2)) =
          (∑ j ∈ Finset.range (k + 1),
             (1 : ℝ) / ((j : ℝ) ^ 2 + a ^ 2)) +
             1 / (((k : ℝ) + 1) ^ 2 + a ^ 2) := by
            rw [Finset.sum_range_succ]
            simp only [Nat.cast_succ]
        _ ≤ (1 / a ^ 2 + 2 / a - 2 / (a + (k : ℝ))) +
               (2 / (a + (k : ℝ)) - 2 / (a + (k : ℝ) + 1)) :=
          add_le_add ih (reciprocal_quadratic_step a ha k)
        _ = 1 / a ^ 2 + 2 / a - 2 / (a + (Nat.succ k : ℝ)) := by
          simp only [Nat.cast_succ]
          ring
  have ha0 : 0 < a := by linarith
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha0
  have hfirst : (1 : ℝ) / a ^ 2 ≤ 1 / a := by
    apply (div_le_div_iff₀ ha2 ha0).2
    nlinarith [mul_nonneg (le_of_lt ha0) (sub_nonneg.mpr (by linarith : 0 ≤ a - 1))]
  have hnonneg : 0 ≤ (2 : ℝ) / (a + (n : ℝ)) := by positivity
  calc
    (∑ j ∈ Finset.range (n + 1), (1 : ℝ) / ((j : ℝ) ^ 2 + a ^ 2)) ≤
        1 / a ^ 2 + 2 / a - 2 / (a + (n : ℝ)) := hprefix n
    _ ≤ 1 / a + 2 / a := by linarith
    _ = 3 / a := by ring

/-- The finite quadratic majorant survives any nonnegative horizontal shift.
This is the real-denominator bridge needed when `x = z.re` in the finite
complex reciprocal/log comparison. The upstream V2 proof body is unchanged. -/
theorem shifted_reciprocal_quadratic_range_bound
    (a x : ℝ) (ha : 1 ≤ a) (hx : 0 ≤ x) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
        (1 : ℝ) / (((j : ℝ) + x) ^ 2 + a ^ 2)) ≤ 3 / a := by
  have hshift : ∀ j : ℕ,
      (1 : ℝ) / (((j : ℝ) + x) ^ 2 + a ^ 2) ≤
        1 / ((j : ℝ) ^ 2 + a ^ 2) := by
    intro j
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
    have hjx : 0 ≤ (j : ℝ) * x := mul_nonneg hj hx
    have hs : (j : ℝ) ^ 2 ≤ ((j : ℝ) + x) ^ 2 := by
      nlinarith [sq_nonneg x]
    have hden : 0 < (j : ℝ) ^ 2 + a ^ 2 := by positivity
    exact one_div_le_one_div_of_le hden (by nlinarith)
  calc
    (∑ j ∈ Finset.range (n + 1),
       (1 : ℝ) / (((j : ℝ) + x) ^ 2 + a ^ 2)) ≤
      (∑ j ∈ Finset.range (n + 1),
       (1 : ℝ) / ((j : ℝ) ^ 2 + a ^ 2)) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hshift j
    _ ≤ 3 / a := reciprocal_quadratic_range_bound a ha n

end RiemannVonMangoldt
end P2MFinalSource040

/- Source module: UnitIntervalLogShiftV1
   Original SHA256: 15efe9d17e9588be57d2419fdfbacd2d069e4ae87958e5d3b507bd9323296626 -/
section P2MFinalSource041

set_option autoImplicit false
namespace RiemannVonMangoldt

/-- Exact shifted unit-interval complex logarithm increment; the upper
endpoint is `j+1` rather than `j`. -/
theorem reciprocal_unit_interval_log_increment
    (z : ℂ) (hz : 0 < z.re) (ht : z.im ≠ 0) (j : ℕ) :
    (∫ u in (0 : ℝ)..1, (z + (j : ℂ) + (u : ℂ))⁻¹) =
      Complex.log (z + ((j + 1 : ℕ) : ℂ)) - Complex.log (z + (j : ℂ)) := by
  have hzj : 0 < (z + (j : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
    linarith
  have htj : (z + (j : ℂ)).im ≠ 0 := by
    simpa only [Complex.add_im, Complex.natCast_im, add_zero] using ht
  have h := reciprocal_interval_integral_log (z + (j : ℂ)) hzj htj
    0 1 (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

end RiemannVonMangoldt
end P2MFinalSource041

/- Source module: FiniteReciprocalLogV2
   Original SHA256: cb148902b3df969e23b9b6148071fbdc4c7909887382bd5cc9033eac330b78c3 -/
section P2MFinalSource042

set_option autoImplicit false
namespace RiemannVonMangoldt

/-- Exact finite Euler reciprocal-sum/principal-log comparison.
No Gamma limit, analytic continuation or unstated zero-count premise is used. -/
theorem finite_reciprocal_sum_log_bound
    (z : ℂ) (hz : 0 < z.re) (hIm : 1 ≤ |z.im|) (n : ℕ) :
    ‖(∑ j ∈ Finset.range (n + 1), (z + (j : ℂ))⁻¹) -
        (Complex.log (z + ((n + 1 : ℕ) : ℂ)) - Complex.log z)‖ ≤
      3 / |z.im| := by
  have hi : z.im ≠ 0 := by
    intro h
    norm_num [h] at hIm
  have hlogsum :
      (∑ j ∈ Finset.range (n + 1),
        ∫ u in (0 : ℝ)..1, (z + (j : ℂ) + (u : ℂ))⁻¹) =
      Complex.log (z + ((n + 1 : ℕ) : ℂ)) - Complex.log z := by
    calc
      _ = ∑ j ∈ Finset.range (n + 1),
          (Complex.log (z + ((j + 1 : ℕ) : ℂ)) -
            Complex.log (z + (j : ℂ))) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact reciprocal_unit_interval_log_increment z hz hi j
      _ = Complex.log (z + ((n + 1 : ℕ) : ℂ)) - Complex.log z := by
            simpa using (Finset.sum_range_sub
              (fun j : ℕ => Complex.log (z + (j : ℂ))) (n + 1))
  have hsingle (j : ℕ) :
      ‖(z + (j : ℂ))⁻¹ -
          (∫ u in (0 : ℝ)..1, (z + (j : ℂ) + (u : ℂ))⁻¹)‖ ≤
        1 / (((j : ℝ) + z.re) ^ 2 + |z.im| ^ 2) := by
    have hw : 0 < (z + (j : ℂ)).re := by
      simp only [Complex.add_re, Complex.natCast_re]
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
      linarith
    have hwi : (z + (j : ℂ)).im ≠ 0 := by
      simpa only [Complex.add_im, Complex.natCast_im, add_zero] using hi
    have h := reciprocal_unit_integral_error (z + (j : ℂ)) hw hwi
    simpa only [Complex.add_re, Complex.natCast_re, Complex.add_im,
      Complex.natCast_im, add_zero, sq_abs, add_comm] using h
  calc
    ‖(∑ j ∈ Finset.range (n + 1), (z + (j : ℂ))⁻¹) -
        (Complex.log (z + ((n + 1 : ℕ) : ℂ)) - Complex.log z)‖ =
        ‖∑ j ∈ Finset.range (n + 1),
            ((z + (j : ℂ))⁻¹ -
              (∫ u in (0 : ℝ)..1, (z + (j : ℂ) + (u : ℂ))⁻¹))‖ := by
          rw [← hlogsum, Finset.sum_sub_distrib]
    _ ≤ ∑ j ∈ Finset.range (n + 1),
          (1 : ℝ) / (((j : ℝ) + z.re) ^ 2 + |z.im| ^ 2) := by
          calc
            _ ≤ ∑ j ∈ Finset.range (n + 1),
                  ‖(z + (j : ℂ))⁻¹ -
                      (∫ u in (0 : ℝ)..1, (z + (j : ℂ) + (u : ℂ))⁻¹)‖ :=
                        norm_sum_le _ _
            _ ≤ ∑ j ∈ Finset.range (n + 1),
                  (1 : ℝ) / (((j : ℝ) + z.re) ^ 2 + |z.im| ^ 2) := by
                    apply Finset.sum_le_sum
                    intro j hj
                    exact hsingle j
    _ ≤ 3 / |z.im| :=
          shifted_reciprocal_quadratic_range_bound |z.im| z.re hIm (le_of_lt hz) n

end RiemannVonMangoldt
end P2MFinalSource042

/- Source module: GammaEndpointCorrectionV1
   Original SHA256: f5c1718a3c5d2e134bfff352be80aea2e83850542ba235ecfc93f92ddf9bd013 -/
section P2MFinalSource043

set_option autoImplicit false
namespace RiemannVonMangoldt

/-- The exact `log n` normalization of the accepted Euler supplier differs from
    the finite reciprocal/log telescope's endpoint `log (z+n+1)` by O(1/n).
    This lemma contains no Gamma or Dirichlet-character hypotheses. -/
theorem gamma_endpoint_log_correction
    (z : ℂ) (hz : 0 < z.re) (n : ℕ) (hn : 0 < n)
    (hlarge : 2 * ‖z + 1‖ ≤ (n : ℝ)) :
    ‖Complex.log (n : ℂ) - Complex.log (z + ((n + 1 : ℕ) : ℂ))‖ ≤
      (3 / 2 : ℝ) * (‖z + 1‖ / (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  let w : ℂ := (z + 1) / (n : ℂ)
  have hwnorm : ‖w‖ = ‖z + 1‖ / (n : ℝ) := by
    simp [w, norm_div]
  have hw : ‖w‖ ≤ (1 / 2 : ℝ) := by
    rw [hwnorm]
    apply (div_le_iff₀ hnR).mpr
    linarith
  have hwzero : 1 + w ≠ 0 := by
    intro h
    have hneg : w = -1 := by
      apply add_left_cancel (a := (1 : ℂ))
      simpa using h
    have hnorm : ‖w‖ = (1 : ℝ) := by rw [hneg]; norm_num
    linarith
  have hscale : (n : ℂ) * (1 + w) = z + ((n + 1 : ℕ) : ℂ) := by
    dsimp [w]
    field_simp
    push_cast
    ring
  have hlog : Complex.log (z + ((n + 1 : ℕ) : ℂ)) =
      Complex.log (n : ℂ) + Complex.log (1 + w) := by
    calc
      Complex.log (z + ((n + 1 : ℕ) : ℂ)) =
          Complex.log ((n : ℝ) * (1 + w)) := by
            congr 1
            exact hscale.symm
      _ = (Real.log (n : ℝ) : ℂ) + Complex.log (1 + w) :=
        Complex.log_ofReal_mul hnR hwzero
      _ = Complex.log (n : ℂ) + Complex.log (1 + w) := by
        rw [Complex.natCast_log]
  have hdiff : Complex.log (n : ℂ) -
      Complex.log (z + ((n + 1 : ℕ) : ℂ)) = -Complex.log (1 + w) := by
    rw [hlog]
    ring
  rw [hdiff, norm_neg]
  calc
    ‖Complex.log (1 + w)‖ ≤ (3 / 2 : ℝ) * ‖w‖ :=
      Complex.norm_log_one_add_half_le_self hw
    _ = (3 / 2 : ℝ) * (‖z + 1‖ / (n : ℝ)) := by rw [hwnorm]

end RiemannVonMangoldt
end P2MFinalSource043

/- Source module: GammaFiniteEulerBridgeV1
   Original SHA256: 41036af0d5bbb6ba6c0d5c1459ffd617267cc9b4fee5e068dfaa1c97b29d309e -/
section P2MFinalSource044

set_option autoImplicit false
namespace RiemannVonMangoldt

/-- Exact finite Euler approximation bound, with the necessary `log n`
    normalization and inclusive reciprocal-sum endpoint. This is the
    finite input for the genuine accepted GammaSeq convergence theorem. -/
theorem gamma_finite_euler_log_bound
    (z : ℂ) (hz : 0 < z.re) (hIm : 1 ≤ |z.im|)
    (n : ℕ) (hn : 0 < n) (hlarge : 2 * ‖z + 1‖ ≤ (n : ℝ)) :
    ‖(Complex.log (n : ℂ) -
        ∑ j ∈ Finset.range (n + 1), (z + (j : ℂ))⁻¹) - Complex.log z‖ ≤
      3 / |z.im| + (3 / 2 : ℝ) * (‖z + 1‖ / (n : ℝ)) := by
  have hc := gamma_endpoint_log_correction z hz n hn hlarge
  have hf := finite_reciprocal_sum_log_bound z hz hIm n
  calc
    ‖(Complex.log (n : ℂ) -
        ∑ j ∈ Finset.range (n + 1), (z + (j : ℂ))⁻¹) - Complex.log z‖ =
      ‖(Complex.log (n : ℂ) - Complex.log (z + ((n + 1 : ℕ) : ℂ))) -
        ((∑ j ∈ Finset.range (n + 1), (z + (j : ℂ))⁻¹) -
          (Complex.log (z + ((n + 1 : ℕ) : ℂ)) - Complex.log z))‖ := by
            congr 1
            ring
    _ ≤ ‖Complex.log (n : ℂ) - Complex.log (z + ((n + 1 : ℕ) : ℂ))‖ +
      ‖(∑ j ∈ Finset.range (n + 1), (z + (j : ℂ))⁻¹) -
        (Complex.log (z + ((n + 1 : ℕ) : ℂ)) - Complex.log z)‖ :=
          norm_sub_le _ _
    _ ≤ (3 / 2 : ℝ) * (‖z + 1‖ / (n : ℝ)) + 3 / |z.im| :=
          add_le_add hc hf
    _ = 3 / |z.im| + (3 / 2 : ℝ) * (‖z + 1‖ / (n : ℝ)) := by ring

end RiemannVonMangoldt
end P2MFinalSource044

/- Source module: GammaParityCorrectionV1
   Original SHA256: c0a501fb92da05ceaa3e68475815be6bc0393d559279ab129fa206bf4ed02fc5 -/
section P2MFinalSource045

set_option autoImplicit false
namespace RiemannVonMangoldt
open scoped Classical

/-- A scalar parity-error majorant. The input a is the real part of twice
the half-shifted Gamma argument, not a surrogate for the Dirichlet
gammaFactor itself. No small-u assumption is made. -/
theorem gamma_scalar_parity_error_bound
    (a t : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 5 / 2) (ht : 2 ≤ t) :
    0 ≤ Real.log (1 + a ^ 2 / t ^ 2) / 4 ∧
      Real.log (1 + a ^ 2 / t ^ 2) / 4 ≤
        25 / (16 * t ^ 2) := by
  have htpos : 0 < t := by linarith
  have ht_sq : 0 < t ^ 2 := sq_pos_of_pos htpos
  have hu : 0 ≤ a ^ 2 / t ^ 2 := div_nonneg (sq_nonneg a) ht_sq.le
  have hlow : 0 ≤ Real.log (1 + a ^ 2 / t ^ 2) :=
    Real.log_nonneg (by linarith)
  have hlog : Real.log (1 + a ^ 2 / t ^ 2) ≤ a ^ 2 / t ^ 2 := by
    have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + a ^ 2 / t ^ 2)
    linarith
  have ha_sq : a ^ 2 ≤ (25 / 4 : ℝ) := by
    nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha)]
  have hrat : a ^ 2 / t ^ 2 ≤ (25 / 4 : ℝ) / t ^ 2 :=
    div_le_div_of_nonneg_right ha_sq ht_sq.le
  constructor
  · linarith
  · calc
      Real.log (1 + a ^ 2 / t ^ 2) / 4 ≤
          (a ^ 2 / t ^ 2) / 4 := div_le_div_of_nonneg_right hlog (by norm_num)
      _ ≤ ((25 / 4 : ℝ) / t ^ 2) / 4 :=
          div_le_div_of_nonneg_right hrat (by norm_num)
      _ = 25 / (16 * t ^ 2) := by ring

/-- Character parity yields a conductor-uniform 25/(16*t²) correction,
including q=1 and the endpoint t=2. -/
theorem gamma_character_parity_error_bound
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) (ht : 2 ≤ t) :
    let a : ℝ := if χ.Even then 3 / 2 else 5 / 2
    0 ≤ Real.log (1 + a ^ 2 / t ^ 2) / 4 ∧
      Real.log (1 + a ^ 2 / t ^ 2) / 4 ≤
        25 / (16 * t ^ 2) := by
  classical
  dsimp
  by_cases he : χ.Even
  · simpa only [if_pos he] using
      gamma_scalar_parity_error_bound (3 / 2) t (by norm_num) (by norm_num) ht
  · simpa only [if_neg he] using
      gamma_scalar_parity_error_bound (5 / 2) t (by norm_num) (by norm_num) ht

end RiemannVonMangoldt
end P2MFinalSource045

/- Source module: GammaScalarCalculusV4
   Original SHA256: fda93a404ce85396393f0b3c9650a9b15c31855cd704fd965495a3d2b46dbabe -/
section P2MFinalSource046

set_option autoImplicit false
namespace RiemannVonMangoldt
open MeasureTheory

/-- The endpoint-correct logarithm integral used by the Gamma/level main
    term, specialized from Mathlib's original integral_log theorem. -/
theorem integral_log_from_two (T : ℝ) (_hT : 2 ≤ T) :
    (∫ t in (2 : ℝ)..T, Real.log t) =
      (T * Real.log T - T) - (2 * Real.log 2 - 2) := by
  rw [integral_log]
  ring

/-- The exact reciprocal-square integral supplies the uniform odd-parity
    correction, including the endpoint T=2. -/
theorem integral_inv_sq_from_two (T : ℝ) (hT : 2 ≤ T) :
    (∫ t in (2 : ℝ)..T, (1 : ℝ) / t ^ 2) =
      (1 / 2 : ℝ) - 1 / T := by
  have hcont : ContinuousOn (fun t : ℝ => (1 : ℝ) / t ^ 2)
      (Set.uIcc (2 : ℝ) T) := by
    apply continuousOn_const.div (continuousOn_id.pow 2)
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    exact pow_ne_zero _ (ne_of_gt
      (lt_of_lt_of_le (by norm_num) ht.1))
  have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) T,
      HasDerivAt (fun x : ℝ => -(x⁻¹)) ((1 : ℝ) / t ^ 2) t := by
    intro t ht
    have htne : t ≠ 0 := by
      rw [Set.uIcc_of_le hT] at ht
      exact ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1)
    simpa only [Pi.neg_apply, neg_neg, one_div] using!
      (hasDerivAt_inv htne).neg
  convert intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv hcont.intervalIntegrable using 1 <;> norm_num [one_div] <;> ring

end RiemannVonMangoldt
end P2MFinalSource046

/- Source module: GammaScalarMainV2
   Original SHA256: 1ac75c2560c873f7c3372ced1eec1316a600afe8d887cd55d82edaf241e54d6c -/
section P2MFinalSource047

set_option autoImplicit false
namespace RiemannVonMangoldt
open MeasureTheory

/-- Exact affine-logarithm integral, for the coefficient that combines the
    modulus term with the real Gamma-factor main term. The constant is
    arbitrary; in the parent it is log(q) - log(2*pi). Both endpoints persist. -/
theorem integral_affine_log_half_from_two
    (c T : ℝ) (hT : 2 ≤ T) :
    (∫ t in (2 : ℝ)..T, (Real.log t + c) / 2) =
      (T / 2) * (Real.log T + c - 1) -
        ((2 : ℝ) / 2) * (Real.log 2 + c - 1) := by
  rw [intervalIntegral.integral_div,
      intervalIntegral.integral_add
        (intervalIntegral.intervalIntegrable_log' : IntervalIntegrable Real.log volume 2 T)
        intervalIntegrable_const,
      integral_log]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

end RiemannVonMangoldt
end P2MFinalSource047

/- Source module: GammaLevelMainV1
   Original SHA256: dc5eecadda54154c9c25d53cd8c6d54e29a297c6822556be2989ee73bc581468 -/
section P2MFinalSource048

set_option autoImplicit false
namespace RiemannVonMangoldt
open MeasureTheory

/-- Retain q and the crucial exponential factor exactly. -/
lemma gamma_level_log_normalization
    (q : ℕ) (hq : 1 ≤ q) (t : ℝ) (ht : 0 < t) :
    Real.log ((q : ℝ) * t / (2 * Real.pi * Real.exp 1)) =
      Real.log t + (Real.log (q : ℝ) - Real.log (2 * Real.pi)) - 1 := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast (show 0 < q by omega)
  have hden : (2 : ℝ) * Real.pi ≠ 0 := ne_of_gt (by positivity)
  have hexp : Real.exp (1 : ℝ) ≠ 0 := ne_of_gt (Real.exp_pos 1)
  rw [Real.log_div (mul_ne_zero (ne_of_gt hqpos) (ne_of_gt ht))
    (mul_ne_zero hden hexp)]
  rw [Real.log_mul (ne_of_gt hqpos) (ne_of_gt ht)]
  rw [Real.log_mul hden hexp]
  rw [Real.log_exp]
  ring

/-- The exact normalized scalar main term is an interval antiderivative of
    the modulus plus Gamma logarithm, for every q≥1 and T≥2. -/
theorem gamma_level_main_integral
    (q : ℕ) (hq : 1 ≤ q) (T : ℝ) (hT : 2 ≤ T) :
    (∫ t in (2 : ℝ)..T,
      (Real.log (q : ℝ) + Real.log (t / (2 * Real.pi))) / 2) =
      (T / 2) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) -
        ((2 : ℝ) / 2) * Real.log ((q : ℝ) * 2 / (2 * Real.pi * Real.exp 1)) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast (show 0 < q by omega)
  have hden : (2 : ℝ) * Real.pi ≠ 0 := ne_of_gt (by positivity)
  have hlog : ∀ t ∈ Set.uIcc (2 : ℝ) T,
      (Real.log (q : ℝ) + Real.log (t / (2 * Real.pi))) / 2 =
        (Real.log t + (Real.log (q : ℝ) - Real.log (2 * Real.pi))) / 2 := by
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
    rw [Real.log_div (ne_of_gt htpos) hden]
    ring
  calc
    (∫ t in (2 : ℝ)..T,
      (Real.log (q : ℝ) + Real.log (t / (2 * Real.pi))) / 2) =
        (∫ t in (2 : ℝ)..T,
          (Real.log t + (Real.log (q : ℝ) - Real.log (2 * Real.pi))) / 2) := by
          exact intervalIntegral.integral_congr hlog
    _ = (T / 2) * (Real.log T +
            (Real.log (q : ℝ) - Real.log (2 * Real.pi)) - 1) -
          ((2 : ℝ) / 2) * (Real.log 2 +
            (Real.log (q : ℝ) - Real.log (2 * Real.pi)) - 1) :=
            integral_affine_log_half_from_two _ T hT
    _ = (T / 2) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) -
          ((2 : ℝ) / 2) * Real.log ((q : ℝ) * 2 /
            (2 * Real.pi * Real.exp 1)) := by
          rw [gamma_level_log_normalization q hq T
            (lt_of_lt_of_le (by norm_num) hT),
            gamma_level_log_normalization q hq 2 (by norm_num)]

end RiemannVonMangoldt
end P2MFinalSource048

/- Source module: GammaSharedPrefixChainV1
   Original SHA256: 6f1d1a87d5518c64dcf2c5690b3acebe8c8aa7d180e585dbdb07a31b536e69ac -/
section P2MFinalSource049

/-!
Source-faithful unification of the existing gamma dependency chain.
The exact accepted AcceptedReflectionPrefixV1 supplies the shared Euler
and GammaR declarations once. Every retained module body below is unchanged;
only import lines are removed, and explicit section/namespace boundaries
reproduce the original per-module scope.

This new aggregation requires its own ordinary pinned Lean verification.
It does not inherit kernel approval merely from the constituent sources.
-/

section P2M16GammaSource1

set_option autoImplicit false
namespace RiemannVonMangoldt

/-- An absolute, character-independent Gamma logarithmic-derivative error
    on the right half-plane away from the real axis. The complete Euler
    derivative limit and formula are the original Helfgott accepted lemmas. -/
theorem gamma_log_derivative_main_term
    (z : ℂ) (hz : 0 < z.re) (hIm : 1 ≤ |z.im|) :
    ‖deriv Complex.Gamma z / Complex.Gamma z - Complex.log z‖ ≤
      3 / |z.im| := by
  open Filter in
  have hformula :
      (fun n : ℕ => logDeriv (fun w : ℂ => w.GammaSeq n) z) =ᶠ[Filter.atTop]
        (fun n : ℕ => Complex.log (n : ℂ) -
          ∑ j ∈ Finset.range (n + 1), (z + (j : ℂ))⁻¹) := by
    filter_upwards [Filter.eventually_ne_atTop 0] with n hn
    exact Helfgott.GammaSeq_logDeriv_formula n hn z hz
  have hlim : Filter.Tendsto
      (fun n : ℕ => Complex.log (n : ℂ) -
        ∑ j ∈ Finset.range (n + 1), (z + (j : ℂ))⁻¹)
      Filter.atTop (nhds (logDeriv Complex.Gamma z)) := by
    exact (Helfgott.GammaSeq_logDeriv_tendsto z hz).congr' hformula
  have hlimNorm : Filter.Tendsto
      (fun n : ℕ => ‖(Complex.log (n : ℂ) -
        ∑ j ∈ Finset.range (n + 1), (z + (j : ℂ))⁻¹) - Complex.log z‖)
      Filter.atTop (nhds ‖logDeriv Complex.Gamma z - Complex.log z‖) := by
    exact (hlim.sub tendsto_const_nhds).norm
  have hErr : Filter.Tendsto
      (fun n : ℕ => (3 / 2 : ℝ) * (‖z + 1‖ / (n : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa only [mul_div_assoc] using
      (tendsto_const_div_atTop_nhds_zero_nat ((3 / 2 : ℝ) * ‖z + 1‖))
  have hRHS : Filter.Tendsto
      (fun n : ℕ => 3 / |z.im| + (3 / 2 : ℝ) * (‖z + 1‖ / (n : ℝ)))
      Filter.atTop (nhds (3 / |z.im|)) := by
    simpa using (tendsto_const_nhds.add hErr)
  have hlargeEv : ∀ᶠ n : ℕ in Filter.atTop,
      2 * ‖z + 1‖ ≤ (n : ℝ) := by
    exact (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  have hboundEv : ∀ᶠ n : ℕ in Filter.atTop,
      ‖(Complex.log (n : ℂ) -
        ∑ j ∈ Finset.range (n + 1), (z + (j : ℂ))⁻¹) - Complex.log z‖ ≤
      3 / |z.im| + (3 / 2 : ℝ) * (‖z + 1‖ / (n : ℝ)) := by
    filter_upwards [Filter.eventually_ne_atTop 0, hlargeEv] with n hn hnlarge
    exact gamma_finite_euler_log_bound z hz hIm n (Nat.pos_of_ne_zero hn) hnlarge
  have h := le_of_tendsto_of_tendsto hlimNorm hRHS hboundEv
  simpa only [logDeriv_apply] using h


end RiemannVonMangoldt

end P2M16GammaSource1

section P2M16GammaSource2

set_option autoImplicit false
namespace RiemannVonMangoldt

/-- Transfer the checked Gamma logarithmic-derivative remainder to the
    half-scaled parity-shifted argument required by the completed Dirichlet
    L-function. This is an internal analytic bridge, not a public P2M proof. -/
theorem gamma_log_derivative_half_parity
    (s : ℂ) (δ : ℝ) (hs : 0 < s.re) (hδ : 0 ≤ δ)
    (ht : 2 ≤ |s.im|) :
    ‖deriv Complex.Gamma ((s + (δ : ℂ)) / 2) /
        Complex.Gamma ((s + (δ : ℂ)) / 2) -
        Complex.log ((s + (δ : ℂ)) / 2)‖ ≤
      6 / |s.im| := by
  have hre : 0 < ((s + (δ : ℂ)) / 2).re := by
    simp only [Complex.div_ofNat_re, Complex.add_re, Complex.ofReal_re]
    linarith
  have him : 1 ≤ |((s + (δ : ℂ)) / 2).im| := by
    simp only [Complex.div_ofNat_im, Complex.add_im, Complex.ofReal_im, add_zero]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hmain := gamma_log_derivative_main_term ((s + (δ : ℂ)) / 2) hre him
  have hIm_eq : |((s + (δ : ℂ)) / 2).im| = |s.im| / 2 := by
    simp [Complex.div_ofNat_im, Complex.add_im, abs_div]
  rw [hIm_eq] at hmain
  have hne : |s.im| ≠ 0 := by linarith
  have hrhs : 3 / (|s.im| / 2) = 6 / |s.im| := by
    field_simp [hne]
    ring
  exact hmain.trans_eq hrhs


end RiemannVonMangoldt

end P2M16GammaSource2

section P2M16GammaSource3

set_option autoImplicit false
namespace RiemannVonMangoldt
open scoped Classical

/-- The half-scaled Gamma remainder is uniform over every conductor and
    every Dirichlet character, including the q=1 character, for either
    parity shift. This only handles the Gamma argument, not the derivative
    of the full gammaFactor. It is supporting work, not a P2M acceptance. -/
theorem gamma_log_derivative_parity_uniform
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 0 < s.re) (ht : 2 ≤ |s.im|) :
    ‖deriv Complex.Gamma ((s + ((if χ.Even then 0 else 1 : ℝ) : ℂ)) / 2) /
        Complex.Gamma ((s + ((if χ.Even then 0 else 1 : ℝ) : ℂ)) / 2) -
        Complex.log ((s + ((if χ.Even then 0 else 1 : ℝ) : ℂ)) / 2)‖ ≤
      6 / |s.im| := by
  classical
  by_cases he : χ.Even
  · simpa only [if_pos he] using
      gamma_log_derivative_half_parity s 0 hs (by norm_num) ht
  · simpa only [if_neg he] using
      gamma_log_derivative_half_parity s 1 hs (by norm_num) ht


end RiemannVonMangoldt

end P2M16GammaSource3

section P2M16GammaSource4

set_option autoImplicit false
namespace RiemannVonMangoldt
open scoped Classical

/- Internal support for the original Dirichlet zero-count parent.
   The GammaR derivative identity is credited to raresbuhai/Helfgott.
   The Gamma remainder is independently checked but overlaps existing
   accepted Zeta23 Stirling ingredients and is not claimed as new prior art. -/

lemma gammaR_log_derivative_right_halfplane
    (s : ℂ) (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s = -Complex.log (Real.pi : ℂ) / 2 +
      logDeriv Complex.Gamma (s / 2) / 2 := by
  apply Helfgott.GammaR_logDeriv_formula
  intro m hm
  have hre : s.re / 2 = -(m : ℝ) := by
    simpa using congrArg Complex.re hm
  have hn : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-- Exact logarithmic derivative of the genuine Mathlib gamma factor,
    with both parity branches and the pi normalization retained. -/
theorem gammaFactor_log_derivative_formula
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 0 < s.re) :
    logDeriv χ.gammaFactor s = -Complex.log (Real.pi : ℂ) / 2 +
      logDeriv Complex.Gamma
        ((s + ((if χ.Even then 0 else 1 : ℝ) : ℂ)) / 2) / 2 := by
  classical
  by_cases he : χ.Even
  · have hf : χ.gammaFactor = Complex.Gammaℝ :=
      funext (fun z => he.gammaFactor_def z)
    rw [hf]
    simpa only [if_pos he, Complex.ofReal_zero, add_zero] using
      gammaR_log_derivative_right_halfplane s hs
  · have hf : χ.gammaFactor = (fun z : ℂ => Complex.Gammaℝ (z + 1)) := by
      funext z
      simp only [DirichletCharacter.gammaFactor, if_neg he]
    rw [hf, logDeriv_apply, deriv_comp_add_const]
    simpa only [if_neg he, Complex.ofReal_one, logDeriv_apply] using
      gammaR_log_derivative_right_halfplane (s + 1) (by
        simp only [Complex.add_re, Complex.one_re]
        linarith)

/-- An absolute remainder for the actual Dirichlet gamma factor. The
    numerical constant precedes every conductor and character, including
    conductor one; both signs of the height are covered. Internal support. -/
theorem gammaFactor_log_derivative_main_term
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 0 < s.re) (ht : 2 ≤ |s.im|) :
    ‖deriv χ.gammaFactor s / χ.gammaFactor s -
      (-Complex.log (Real.pi : ℂ) / 2 +
        Complex.log ((s + ((if χ.Even then 0 else 1 : ℝ) : ℂ)) / 2) / 2)‖ ≤
      3 / |s.im| := by
  let z : ℂ := (s + ((if χ.Even then 0 else 1 : ℝ) : ℂ)) / 2
  have h : ‖logDeriv Complex.Gamma z - Complex.log z‖ ≤ 6 / |s.im| := by
    simpa only [z, logDeriv_apply] using
      gamma_log_derivative_parity_uniform q χ s hs ht
  change ‖logDeriv χ.gammaFactor s -
    (-Complex.log (Real.pi : ℂ) / 2 + Complex.log z / 2)‖ ≤ _
  rw [gammaFactor_log_derivative_formula q χ s hs]
  change ‖(-Complex.log (Real.pi : ℂ) / 2 + logDeriv Complex.Gamma z / 2) -
    (-Complex.log (Real.pi : ℂ) / 2 + Complex.log z / 2)‖ ≤ _
  have he : (-Complex.log (Real.pi : ℂ) / 2 + logDeriv Complex.Gamma z / 2) -
      (-Complex.log (Real.pi : ℂ) / 2 + Complex.log z / 2) =
      (logDeriv Complex.Gamma z - Complex.log z) / 2 := by ring
  rw [he]
  calc
    ‖(logDeriv Complex.Gamma z - Complex.log z) / (2 : ℂ)‖ =
        ‖logDeriv Complex.Gamma z - Complex.log z‖ / 2 := by simp [norm_div]
    _ ≤ (6 / |s.im|) / 2 := div_le_div_of_nonneg_right h (by norm_num)
    _ = 3 / |s.im| := by ring


end RiemannVonMangoldt

end P2M16GammaSource4

section P2M16GammaSource5

set_option autoImplicit false
namespace RiemannVonMangoldt
open scoped Classical

/- Internal source-only continuation of the genuine Dirichlet gamma-factor
   estimate. No compilation or public originality claim is made here.
   Continuity and interval integrability are proved from the original Mathlib
   GammaR and gammaFactor definitions before comparing the actual integrals. -/

/-- The reciprocal of GammaR is entire; nonvanishing on the right half-plane
    therefore makes GammaR itself analytic there. -/
lemma gammaR_analyticAt_of_re_pos
    (s : ℂ) (hs : 0 < s.re) : AnalyticAt ℂ Complex.Gammaℝ s := by
  have hAinv : AnalyticAt ℂ (Complex.Gammaℝ)⁻¹ s :=
    Complex.differentiable_Gammaℝ_inv.analyticAt s
  simpa only [inv_inv] using
    hAinv.inv (inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hs))

/-- Analyticity of the original gamma factor, retaining both parity branches. -/
lemma gammaFactor_analyticAt_of_re_pos
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 0 < s.re) : AnalyticAt ℂ χ.gammaFactor s := by
  classical
  by_cases he : χ.Even
  · have hf : χ.gammaFactor = Complex.Gammaℝ :=
      funext (fun z => he.gammaFactor_def z)
    rw [hf]
    exact gammaR_analyticAt_of_re_pos s hs
  · have hf : χ.gammaFactor = (fun z : ℂ => Complex.Gammaℝ (z + 1)) := by
      funext z
      simp only [DirichletCharacter.gammaFactor, if_neg he]
    rw [hf]
    have hs1 : 0 < (s + 1).re := by
      simp only [Complex.add_re, Complex.one_re]
      linarith
    have hshift : AnalyticAt ℂ (fun z : ℂ => z + 1) s :=
      (show Differentiable ℂ (fun z : ℂ => z + 1) from by fun_prop).analyticAt s
    simpa only [Function.comp_def] using
      (gammaR_analyticAt_of_re_pos (s + 1) hs1).comp
        (f := fun z : ℂ => z + 1) (x := s) hshift

/-- Nonvanishing of the same original gamma factor in the right half-plane. -/
lemma gammaFactor_ne_zero_of_re_pos
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 0 < s.re) : χ.gammaFactor s ≠ 0 := by
  classical
  by_cases he : χ.Even
  · rw [he.gammaFactor_def s]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · have hs1 : 0 < (s + 1).re := by
      simp only [Complex.add_re, Complex.one_re]
      linarith
    simpa only [DirichletCharacter.gammaFactor, if_neg he] using
      (Complex.Gammaℝ_ne_zero_of_re_pos hs1)

/-- The genuine logarithmic derivative is continuous, since its numerator is
    the derivative of an analytic function and its denominator is nonzero. -/
lemma gammaFactor_logDeriv_continuousAt_of_re_pos
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 0 < s.re) : ContinuousAt (logDeriv χ.gammaFactor) s := by
  have hA := gammaFactor_analyticAt_of_re_pos q χ s hs
  change ContinuousAt (fun z : ℂ => deriv χ.gammaFactor z / χ.gammaFactor z) s
  exact hA.deriv.continuousAt.div hA.continuousAt
    (gammaFactor_ne_zero_of_re_pos q χ s hs)

/-- Along any vertical line in the positive half-plane, the actual gamma-factor
    remainder is continuous for every real height, including the endpoints of
    any finite integration interval. -/
theorem gammaFactor_vertical_remainder_continuous
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (σ : ℝ) (hσ : 0 < σ) :
    Continuous (fun t : ℝ =>
      logDeriv χ.gammaFactor ((σ : ℂ) + Complex.I * (t : ℂ)) -
        (-Complex.log (Real.pi : ℂ) / 2 +
          Complex.log (((σ : ℂ) + Complex.I * (t : ℂ) +
            ((if χ.Even then 0 else 1 : ℝ) : ℂ)) / 2) / 2)) := by
  classical
  let δ : ℝ := if χ.Even then 0 else 1
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    split_ifs <;> norm_num
  have hpath : Continuous (fun t : ℝ => (σ : ℂ) + Complex.I * (t : ℂ)) := by
    fun_prop
  have harg : Continuous (fun t : ℝ =>
      ((σ : ℂ) + Complex.I * (t : ℂ) + (δ : ℂ)) / 2) := by
    fun_prop
  have hGamma : Continuous (fun t : ℝ =>
      logDeriv χ.gammaFactor ((σ : ℂ) + Complex.I * (t : ℂ))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hre : 0 < ((σ : ℂ) + Complex.I * (t : ℂ)).re := by
      simpa [Complex.mul_re] using hσ
    exact (gammaFactor_logDeriv_continuousAt_of_re_pos q χ _ hre).comp
      (f := fun u : ℝ => (σ : ℂ) + Complex.I * (u : ℂ)) (x := t)
      hpath.continuousAt
  have hlog : Continuous (fun t : ℝ =>
      Complex.log (((σ : ℂ) + Complex.I * (t : ℂ) + (δ : ℂ)) / 2)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hmem : ((σ : ℂ) + Complex.I * (t : ℂ) + (δ : ℂ)) / 2 ∈
        Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      have hre : (((σ : ℂ) + Complex.I * (t : ℂ) + (δ : ℂ)) / 2).re =
          (σ + δ) / 2 := by
        simp [Complex.mul_re]
      rw [hre]
      positivity
    exact (Complex.hasDerivAt_log hmem).continuousAt.comp
      (f := fun u : ℝ => ((σ : ℂ) + Complex.I * (u : ℂ) + (δ : ℂ)) / 2)
      (x := t) harg.continuousAt
  change Continuous (fun t : ℝ =>
    logDeriv χ.gammaFactor ((σ : ℂ) + Complex.I * (t : ℂ)) -
      (-Complex.log (Real.pi : ℂ) / 2 +
        Complex.log (((σ : ℂ) + Complex.I * (t : ℂ) + (δ : ℂ)) / 2) / 2))
  exact hGamma.sub (continuous_const.add (hlog.div_const (2 : ℂ)))

/-- Genuine interval integrability on every finite vertical segment; there is
    no integrability premise carried into the quantitative estimate. -/
theorem gammaFactor_vertical_remainder_intervalIntegrable
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (σ : ℝ) (hσ : 0 < σ) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      logDeriv χ.gammaFactor ((σ : ℂ) + Complex.I * (t : ℂ)) -
        (-Complex.log (Real.pi : ℂ) / 2 +
          Complex.log (((σ : ℂ) + Complex.I * (t : ℂ) +
            ((if χ.Even then 0 else 1 : ℝ) : ℂ)) / 2) / 2))
      MeasureTheory.volume a b :=
  (gammaFactor_vertical_remainder_continuous q χ σ hσ).intervalIntegrable a b

/-- Integrating the uniform gamma-factor remainder from height 2 to T gives
    the explicit logarithmic error. This covers every character of every
    positive conductor and retains the genuine parity and pi normalization. -/
theorem gammaFactor_vertical_integrated_remainder
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (σ T : ℝ) (hσ : 0 < σ) (hT : 2 ≤ T) :
    ‖∫ t in (2 : ℝ)..T,
      logDeriv χ.gammaFactor ((σ : ℂ) + Complex.I * (t : ℂ)) -
        (-Complex.log (Real.pi : ℂ) / 2 +
          Complex.log (((σ : ℂ) + Complex.I * (t : ℂ) +
            ((if χ.Even then 0 else 1 : ℝ) : ℂ)) / 2) / 2)‖ ≤
      3 * (Real.log T - Real.log 2) := by
  let f : ℝ → ℂ := fun t =>
    logDeriv χ.gammaFactor ((σ : ℂ) + Complex.I * (t : ℂ)) -
      (-Complex.log (Real.pi : ℂ) / 2 +
        Complex.log (((σ : ℂ) + Complex.I * (t : ℂ) +
          ((if χ.Even then 0 else 1 : ℝ) : ℂ)) / 2) / 2)
  have hf : IntervalIntegrable f MeasureTheory.volume 2 T :=
    gammaFactor_vertical_remainder_intervalIntegrable q χ σ hσ 2 T
  have hmajorCont : ContinuousOn (fun t : ℝ => (3 : ℝ) / t) (Set.uIcc 2 T) := by
    apply continuousOn_const.div continuousOn_id
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) ht.1)
  have hmajor : IntervalIntegrable (fun t : ℝ => (3 : ℝ) / t)
      MeasureTheory.volume 2 T := hmajorCont.intervalIntegrable
  have hpoint : ∀ t ∈ Set.Icc (2 : ℝ) T, ‖f t‖ ≤ (3 : ℝ) / t := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 2) ht.1
    have hre : 0 < ((σ : ℂ) + Complex.I * (t : ℂ)).re := by
      simpa [Complex.mul_re] using hσ
    have him : ((σ : ℂ) + Complex.I * (t : ℂ)).im = t := by
      simp [Complex.mul_im]
    have hheight : 2 ≤ |((σ : ℂ) + Complex.I * (t : ℂ)).im| := by
      rw [him, abs_of_nonneg ht0]
      exact ht.1
    have h := gammaFactor_log_derivative_main_term q χ
      ((σ : ℂ) + Complex.I * (t : ℂ)) hre hheight
    simpa only [f, logDeriv_apply, him, abs_of_nonneg ht0] using h
  have hint : (∫ t in (2 : ℝ)..T, (3 : ℝ) / t) =
      3 * (Real.log T - Real.log 2) := by
    have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) T,
        HasDerivAt (fun x : ℝ => 3 * Real.log x) (3 / t) t := by
      intro t ht
      rw [Set.uIcc_of_le hT] at ht
      have htne : t ≠ 0 :=
        ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) ht.1)
      simpa only [div_eq_mul_inv] using (Real.hasDerivAt_log htne).const_mul (3 : ℝ)
    calc
      (∫ t in (2 : ℝ)..T, (3 : ℝ) / t) = 3 * Real.log T - 3 * Real.log 2 :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hmajor
      _ = 3 * (Real.log T - Real.log 2) := by ring
  change ‖∫ t in (2 : ℝ)..T, f t‖ ≤ _
  calc
    ‖∫ t in (2 : ℝ)..T, f t‖ ≤ ∫ t in (2 : ℝ)..T, ‖f t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hT
    _ ≤ ∫ t in (2 : ℝ)..T, (3 : ℝ) / t :=
      intervalIntegral.integral_mono_on hT hf.norm hmajor hpoint
    _ = 3 * (Real.log T - Real.log 2) := hint

end RiemannVonMangoldt


end P2M16GammaSource5

section P2M16GammaSource6

set_option autoImplicit false
namespace RiemannVonMangoldt
open scoped Classical

/- Source-only draft of the missing real logarithm normalization.
   Root must kernel-check this exact source in the pinned P2M environment.
   This file uses the original Complex.log and Dirichlet gammaFactor.
   No complex logarithm product identity or branch-additivity claim is used.
   The genuine GammaR derivative input remains credited to raresbuhai/Helfgott.
   This elementary component is internal parent support, not a new public result. -/

/-- Exact real part of the logarithmic Gamma model. The scalar `a` may be
    arbitrary; positive height suffices for the real logarithm identities. -/
theorem gamma_scalar_log_model_re
    (a t : ℝ) (ht : 0 < t) :
    (-Complex.log (Real.pi : ℂ) / 2 +
      Complex.log (((a : ℂ) + Complex.I * (t : ℂ)) / 2) / 2).re =
      Real.log (t / (2 * Real.pi)) / 2 +
        Real.log (1 + a ^ 2 / t ^ 2) / 4 := by
  let z : ℂ := ((a : ℂ) + Complex.I * (t : ℂ)) / 2
  have htne : t ≠ 0 := ne_of_gt ht
  have ht2pos : 0 < t / 2 := by positivity
  have hupos : 0 < 1 + a ^ 2 / t ^ 2 := by
    have hu : 0 ≤ a ^ 2 / t ^ 2 :=
      div_nonneg (sq_nonneg a) (sq_nonneg t)
    linarith
  have hre : z.re = a / 2 := by
    simp [z, Complex.mul_re]
  have him : z.im = t / 2 := by
    simp [z, Complex.mul_im]
  have hnormsq : ‖z‖ ^ 2 = (t / 2) ^ 2 * (1 + a ^ 2 / t ^ 2) := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    field_simp [htne]
    <;> ring
  have hlogs : 2 * Real.log ‖z‖ =
      2 * Real.log (t / 2) + Real.log (1 + a ^ 2 / t ^ 2) := by
    have h := congrArg Real.log hnormsq
    rw [Real.log_pow,
      Real.log_mul (pow_ne_zero 2 (ne_of_gt ht2pos)) (ne_of_gt hupos),
      Real.log_pow] at h
    norm_num at h
    exact h
  have hfrac : t / (2 * Real.pi) = (t / 2) / Real.pi := by ring
  have hlogfrac : Real.log (t / (2 * Real.pi)) =
      Real.log (t / 2) - Real.log Real.pi := by
    rw [hfrac, Real.log_div (ne_of_gt ht2pos) (ne_of_gt Real.pi_pos)]
  have hmodel :
      (-Complex.log (Real.pi : ℂ) / 2 + Complex.log z / 2).re =
        -Real.log Real.pi / 2 + Real.log ‖z‖ / 2 := by
    simp [Complex.log_re, abs_of_pos Real.pi_pos]
  change (-Complex.log (Real.pi : ℂ) / 2 + Complex.log z / 2).re = _
  rw [hmodel, hlogfrac]
  linarith [hlogs]

/-- The exact parity normalization used by the genuine gammaFactor
    remainder at real part `3/2`, including modulus one and height two. -/
theorem gamma_character_log_model_re
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) (ht : 2 ≤ t) :
    let a : ℝ := if χ.Even then 3 / 2 else 5 / 2
    (-Complex.log (Real.pi : ℂ) / 2 +
      Complex.log (((3 / 2 : ℂ) + Complex.I * (t : ℂ) +
        ((if χ.Even then 0 else 1 : ℝ) : ℂ)) / 2) / 2).re =
      Real.log (t / (2 * Real.pi)) / 2 +
        Real.log (1 + a ^ 2 / t ^ 2) / 4 := by
  classical
  let a : ℝ := if χ.Even then 3 / 2 else 5 / 2
  have htpos : 0 < t := by linarith
  have harg :
      ((3 / 2 : ℂ) + Complex.I * (t : ℂ) +
        ((if χ.Even then 0 else 1 : ℝ) : ℂ)) / 2 =
        ((a : ℂ) + Complex.I * (t : ℂ)) / 2 := by
    dsimp [a]
    split_ifs <;> push_cast <;> ring
  change (-Complex.log (Real.pi : ℂ) / 2 +
      Complex.log (((3 / 2 : ℂ) + Complex.I * (t : ℂ) +
        ((if χ.Even then 0 else 1 : ℝ) : ℂ)) / 2) / 2).re =
      Real.log (t / (2 * Real.pi)) / 2 +
        Real.log (1 + a ^ 2 / t ^ 2) / 4
  rw [harg]
  exact gamma_scalar_log_model_re a t htpos

/-- The original logarithmic derivative decomposes into the real main
    model, its exact parity correction, and the original complex remainder.
    No estimate or integrability premise is introduced by this identity. -/
theorem gammaFactor_vertical_real_decomposition
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) (ht : 2 ≤ t) :
    let a : ℝ := if χ.Even then 3 / 2 else 5 / 2
    let ε : ℂ :=
      logDeriv χ.gammaFactor ((3 / 2 : ℂ) + Complex.I * (t : ℂ)) -
        (-Complex.log (Real.pi : ℂ) / 2 +
          Complex.log (((3 / 2 : ℂ) + Complex.I * (t : ℂ) +
            ((if χ.Even then 0 else 1 : ℝ) : ℂ)) / 2) / 2)
    (logDeriv χ.gammaFactor ((3 / 2 : ℂ) + Complex.I * (t : ℂ))).re =
      Real.log (t / (2 * Real.pi)) / 2 +
        Real.log (1 + a ^ 2 / t ^ 2) / 4 + ε.re := by
  classical
  have h := gamma_character_log_model_re q χ t ht
  dsimp only at h ⊢
  rw [Complex.sub_re, h]
  ring


end RiemannVonMangoldt

end P2M16GammaSource6

section P2M16GammaSource7

set_option autoImplicit false
namespace RiemannVonMangoldt
open MeasureTheory
open scoped Classical

/- Uncompiled assembly draft for the exact Gamma/level integral contract.
   All functions are the original Mathlib functions, and every integrability
   obligation is discharged rather than assumed. The exact lower endpoint
   M(q,2) and uniform constants 3 and 25/16 are retained. The genuine GammaR
   and Euler supplier inputs remain credited to raresbuhai/Helfgott, with
   accepted Zeta23 overlap acknowledged in the imported baseline sources.
   This source is internal parent work and claims no public originality. -/

/-- The scalar parity correction is genuinely integrable on the prescribed
    positive interval. No restriction on `a` is needed for integrability. -/
theorem gamma_scalar_parity_intervalIntegrable
    (a T : ℝ) (hT : 2 ≤ T) :
    IntervalIntegrable (fun t : ℝ => Real.log (1 + a ^ 2 / t ^ 2) / 4)
      volume 2 T := by
  have hden : ∀ t ∈ Set.uIcc (2 : ℝ) T, t ^ 2 ≠ 0 := by
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1))
  have hu : ContinuousOn (fun t : ℝ => 1 + a ^ 2 / t ^ 2)
      (Set.uIcc (2 : ℝ) T) :=
    continuousOn_const.add
      (continuousOn_const.div (continuousOn_id.pow 2) hden)
  have hlog : ContinuousOn (fun t : ℝ => Real.log (1 + a ^ 2 / t ^ 2))
      (Set.uIcc (2 : ℝ) T) := by
    apply hu.log
    intro t _
    have hnonneg : 0 ≤ a ^ 2 / t ^ 2 :=
      div_nonneg (sq_nonneg a) (sq_nonneg t)
    exact ne_of_gt (by linarith : 0 < 1 + a ^ 2 / t ^ 2)
  exact (hlog.div_const 4).intervalIntegrable

/-- The unrestricted pointwise parity correction integrates to its exact
    reciprocal-square majorant, including the zero-length endpoint T=2. -/
theorem gamma_scalar_parity_integral_bound
    (a T : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 5 / 2) (hT : 2 ≤ T) :
    0 ≤ (∫ t in (2 : ℝ)..T, Real.log (1 + a ^ 2 / t ^ 2) / 4) ∧
      (∫ t in (2 : ℝ)..T, Real.log (1 + a ^ 2 / t ^ 2) / 4) ≤
        (25 / 16 : ℝ) * ((1 / 2 : ℝ) - 1 / T) := by
  let b : ℝ → ℝ := fun t => Real.log (1 + a ^ 2 / t ^ 2) / 4
  let m : ℝ → ℝ := fun t => 25 / (16 * t ^ 2)
  have hb : IntervalIntegrable b volume 2 T :=
    gamma_scalar_parity_intervalIntegrable a T hT
  have hm_cont : ContinuousOn m (Set.uIcc (2 : ℝ) T) := by
    apply continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 2))
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    have htne : t ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1)
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ htne)
  have hm : IntervalIntegrable m volume 2 T := hm_cont.intervalIntegrable
  have hzero : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 2 T :=
    (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))).intervalIntegrable 2 T
  have hlo : 0 ≤ ∫ t in (2 : ℝ)..T, b t := by
    have h := intervalIntegral.integral_mono_on hT hzero hb (by
      intro t ht
      exact (gamma_scalar_parity_error_bound a t ha0 ha ht.1).1)
    simpa using h
  have hhi : (∫ t in (2 : ℝ)..T, b t) ≤ ∫ t in (2 : ℝ)..T, m t :=
    intervalIntegral.integral_mono_on hT hb hm (by
      intro t ht
      exact (gamma_scalar_parity_error_bound a t ha0 ha ht.1).2)
  have hmint : (∫ t in (2 : ℝ)..T, m t) =
      (25 / 16 : ℝ) * ((1 / 2 : ℝ) - 1 / T) := by
    calc
      (∫ t in (2 : ℝ)..T, m t) =
          ∫ t in (2 : ℝ)..T, (25 / 16 : ℝ) * ((1 : ℝ) / t ^ 2) := by
            apply intervalIntegral.integral_congr
            intro t _
            dsimp [m]
            ring
      _ = (25 / 16 : ℝ) * ((1 / 2 : ℝ) - 1 / T) := by
        rw [intervalIntegral.integral_const_mul, integral_inv_sq_from_two T hT]
  change 0 ≤ (∫ t in (2 : ℝ)..T, b t) ∧
    (∫ t in (2 : ℝ)..T, b t) ≤ _
  exact ⟨hlo, hhi.trans_eq hmint⟩

/-- Continuity of the actual level-plus-gammaFactor integrand on the entire
    vertical line Re(s)=3/2. This proves its finite-interval integrability. -/
theorem gammaFactor_level_integrand_continuous
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    Continuous (fun t : ℝ =>
      (1 / 2 : ℝ) * Real.log (q : ℝ) +
        (logDeriv χ.gammaFactor
          ((3 / 2 : ℂ) + Complex.I * (t : ℂ))).re) := by
  have hpath : Continuous (fun t : ℝ =>
      (3 / 2 : ℂ) + Complex.I * (t : ℂ)) := by fun_prop
  have hgamma : Continuous (fun t : ℝ =>
      logDeriv χ.gammaFactor ((3 / 2 : ℂ) + Complex.I * (t : ℂ))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hre : 0 < ((3 / 2 : ℂ) + Complex.I * (t : ℂ)).re := by
      norm_num [Complex.mul_re]
    exact (gammaFactor_logDeriv_continuousAt_of_re_pos q χ _ hre).comp
      (f := fun u : ℝ => (3 / 2 : ℂ) + Complex.I * (u : ℂ)) (x := t)
      hpath.continuousAt
  exact continuous_const.add (Complex.continuous_re.comp hgamma)

/-- Actual integrability of the prescribed integrand, with no added
    integrability premise and no parity or primitivity restriction. -/
theorem gammaFactor_level_integrand_intervalIntegrable
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (A B : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      (1 / 2 : ℝ) * Real.log (q : ℝ) +
        (logDeriv χ.gammaFactor
          ((3 / 2 : ℂ) + Complex.I * (t : ℂ))).re) volume A B :=
  (gammaFactor_level_integrand_continuous q χ).intervalIntegrable A B

/-- Exact all-level Gamma-factor main-term integral, retaining both
    endpoints and the absolute uniform error constants. This is a real dt
    integral and makes no contour-orientation or zero-count assertion. -/
theorem gammaFactor_level_main_integral_bound
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) (hT : 2 ≤ T) :
    let F : ℝ → ℝ := fun t =>
      (1 / 2 : ℝ) * Real.log (q : ℝ) +
        (logDeriv χ.gammaFactor
          ((3 / 2 : ℂ) + Complex.I * (t : ℂ))).re
    let M : ℝ → ℝ := fun t =>
      (t / 2) * Real.log ((q : ℝ) * t / (2 * Real.pi * Real.exp 1))
    |(∫ t in (2 : ℝ)..T, F t) - (M T - M 2)| ≤
      3 * (Real.log T - Real.log 2) +
        (25 / 16 : ℝ) * ((1 / 2 : ℝ) - 1 / T) := by
  classical
  let a : ℝ := if χ.Even then 3 / 2 else 5 / 2
  let b : ℝ → ℝ := fun t => Real.log (1 + a ^ 2 / t ^ 2) / 4
  let ε : ℝ → ℂ := fun t =>
    logDeriv χ.gammaFactor ((3 / 2 : ℂ) + Complex.I * (t : ℂ)) -
      (-Complex.log (Real.pi : ℂ) / 2 +
        Complex.log (((3 / 2 : ℂ) + Complex.I * (t : ℂ) +
          ((if χ.Even then 0 else 1 : ℝ) : ℂ)) / 2) / 2)
  let g : ℝ → ℝ := fun t =>
    (Real.log (q : ℝ) + Real.log (t / (2 * Real.pi))) / 2
  let F : ℝ → ℝ := fun t =>
    (1 / 2 : ℝ) * Real.log (q : ℝ) +
      (logDeriv χ.gammaFactor ((3 / 2 : ℂ) + Complex.I * (t : ℂ))).re
  let M : ℝ → ℝ := fun t =>
    (t / 2) * Real.log ((q : ℝ) * t / (2 * Real.pi * Real.exp 1))
  have ha0 : 0 ≤ a := by dsimp [a]; split_ifs <;> norm_num
  have ha : a ≤ 5 / 2 := by dsimp [a]; split_ifs <;> norm_num
  have hq : 1 ≤ q := by
    have hqne : q ≠ 0 := NeZero.ne q
    omega
  have hb : IntervalIntegrable b volume 2 T :=
    gamma_scalar_parity_intervalIntegrable a T hT
  have hB : 0 ≤ (∫ t in (2 : ℝ)..T, b t) ∧
      (∫ t in (2 : ℝ)..T, b t) ≤
        (25 / 16 : ℝ) * ((1 / 2 : ℝ) - 1 / T) :=
    gamma_scalar_parity_integral_bound a T ha0 ha hT
  have hεcont : Continuous ε := by
    simpa [ε] using
      gammaFactor_vertical_remainder_continuous q χ (3 / 2) (by norm_num)
  have hε : IntervalIntegrable ε volume 2 T := hεcont.intervalIntegrable 2 T
  have hεre : IntervalIntegrable (fun t : ℝ => (ε t).re) volume 2 T :=
    (Complex.continuous_re.comp hεcont).intervalIntegrable 2 T
  have hF : IntervalIntegrable F volume 2 T :=
    gammaFactor_level_integrand_intervalIntegrable q χ 2 T
  have hg_cont : ContinuousOn g (Set.uIcc (2 : ℝ) T) := by
    have hratio : ContinuousOn (fun t : ℝ => t / (2 * Real.pi))
        (Set.uIcc (2 : ℝ) T) := continuousOn_id.div_const _
    have hlog : ContinuousOn (fun t : ℝ => Real.log (t / (2 * Real.pi)))
        (Set.uIcc (2 : ℝ) T) := by
      apply hratio.log
      intro t ht
      rw [Set.uIcc_of_le hT] at ht
      have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
      exact ne_of_gt (div_pos htpos (by positivity))
    exact (continuousOn_const.add hlog).div_const 2
  have hg : IntervalIntegrable g volume 2 T := hg_cont.intervalIntegrable
  have hpoint : ∀ t ∈ Set.uIcc (2 : ℝ) T, F t = g t + b t + (ε t).re := by
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    have h := gammaFactor_vertical_real_decomposition q χ t ht.1
    change (logDeriv χ.gammaFactor ((3 / 2 : ℂ) + Complex.I * (t : ℂ))).re =
      Real.log (t / (2 * Real.pi)) / 2 + b t + (ε t).re at h
    dsimp only [F, g]
    rw [h]
    ring
  have hsplit : (∫ t in (2 : ℝ)..T, F t) =
      (∫ t in (2 : ℝ)..T, g t) + (∫ t in (2 : ℝ)..T, b t) +
        (∫ t in (2 : ℝ)..T, (ε t).re) := by
    calc
      (∫ t in (2 : ℝ)..T, F t) =
          ∫ t in (2 : ℝ)..T, g t + b t + (ε t).re :=
        intervalIntegral.integral_congr hpoint
      _ = (∫ t in (2 : ℝ)..T, g t) + (∫ t in (2 : ℝ)..T, b t) +
          (∫ t in (2 : ℝ)..T, (ε t).re) := by
        rw [intervalIntegral.integral_add (hg.add hb) hεre,
          intervalIntegral.integral_add hg hb]
  have hmain : (∫ t in (2 : ℝ)..T, g t) = M T - M 2 := by
    simpa [g, M] using gamma_level_main_integral q hq T hT
  have hcomm : (∫ t in (2 : ℝ)..T, (ε t).re) =
      (∫ t in (2 : ℝ)..T, ε t).re := by
    exact intervalIntegral.intervalIntegral_re hε
  have hrem : ‖∫ t in (2 : ℝ)..T, ε t‖ ≤
      3 * (Real.log T - Real.log 2) := by
    simpa [ε] using
      gammaFactor_vertical_integrated_remainder q χ (3 / 2) T (by norm_num) hT
  have herror : (∫ t in (2 : ℝ)..T, F t) - (M T - M 2) =
      (∫ t in (2 : ℝ)..T, ε t).re + (∫ t in (2 : ℝ)..T, b t) := by
    rw [hsplit, hmain, hcomm]
    ring
  change |(∫ t in (2 : ℝ)..T, F t) - (M T - M 2)| ≤ _
  rw [herror]
  calc
    |(∫ t in (2 : ℝ)..T, ε t).re + (∫ t in (2 : ℝ)..T, b t)| ≤
        |(∫ t in (2 : ℝ)..T, ε t).re| + |∫ t in (2 : ℝ)..T, b t| :=
      abs_add_le _ _
    _ ≤ ‖∫ t in (2 : ℝ)..T, ε t‖ + (∫ t in (2 : ℝ)..T, b t) := by
      rw [abs_of_nonneg hB.1]
      exact add_le_add (Complex.abs_re_le_norm _) le_rfl
    _ ≤ 3 * (Real.log T - Real.log 2) +
        (25 / 16 : ℝ) * ((1 / 2 : ℝ) - 1 / T) :=
      add_le_add hrem hB.2

/-- The same exact contract with the explicit positive-modulus hypothesis
    written before the character, as in the frozen mathematical statement. -/
theorem gammaFactor_level_main_integral_bound_of_one_le
    (q : ℕ) (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q)
    (T : ℝ) (hT : 2 ≤ T) :
    let F : ℝ → ℝ := fun t =>
      (1 / 2 : ℝ) * Real.log (q : ℝ) +
        (logDeriv χ.gammaFactor
          ((3 / 2 : ℂ) + Complex.I * (t : ℂ))).re
    let M : ℝ → ℝ := fun t =>
      (t / 2) * Real.log ((q : ℝ) * t / (2 * Real.pi * Real.exp 1))
    |(∫ t in (2 : ℝ)..T, F t) - (M T - M 2)| ≤
      3 * (Real.log T - Real.log 2) +
        (25 / 16 : ℝ) * ((1 / 2 : ℝ) - 1 / T) := by
  letI : NeZero q := ⟨by omega⟩
  exact gammaFactor_level_main_integral_bound q χ T hT


end RiemannVonMangoldt

end P2M16GammaSource7

end P2MFinalSource049

/- Source module: GammaSignedIntegralV3
   Original SHA256: 3dd3166d582ac62cd3dc383121812150843609ffc7aec736e81673824c6aef75 -/
section P2MFinalSource050

open Complex MeasureTheory
open scoped ComplexConjugate
set_option autoImplicit false

namespace RiemannVonMangoldt

/- Internal continuation of the checked upper gamma integral. All integrands
are the original Mathlib gamma factors. The signed extension uses actual
conjugation; its fixed interval is controlled by the two genuine parities.
The imported upper estimate retains its existing supplier attribution. -/

private theorem logDeriv_conj_of_commute
    (f : ℂ → ℂ) (hf : ∀ z, f (conj z) = conj (f z)) (s : ℂ) :
    logDeriv f (conj s) = conj (logDeriv f s) := by
  have hfun : (fun z : ℂ => conj (f (conj z))) = f := by
    funext z
    simp [hf]
  have hd : deriv f (conj s) = conj (deriv f s) := by
    have h := congrFun (deriv_conj_conj (f := f)) (conj s)
    change deriv (fun z : ℂ => conj (f (conj z))) (conj s) =
      conj (deriv f (conj (conj s))) at h
    rw [hfun] at h
    simpa using h
  simp only [logDeriv_apply, hd, hf, map_div₀]

/-- Conjugation of the actual gamma-factor logarithmic derivative throughout
the positive half-plane, obtained from the genuine Gamma formula. -/
theorem gammaFactor_logDeriv_conj
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 0 < s.re) :
    logDeriv χ.gammaFactor (conj s) = conj (logDeriv χ.gammaFactor s) := by
  classical
  have hsc : 0 < (conj s).re := by simpa using hs
  rw [gammaFactor_log_derivative_formula q χ (conj s) hsc,
    gammaFactor_log_derivative_formula q χ s hs]
  have hg : logDeriv Complex.Gamma
      ((conj s + ((if χ.Even then 0 else 1 : ℝ) : ℂ)) / 2) =
      conj (logDeriv Complex.Gamma
        ((s + ((if χ.Even then 0 else 1 : ℝ) : ℂ)) / 2)) := by
    simpa [Complex.conj_ofNat] using logDeriv_conj_of_commute Complex.Gamma Complex.Gamma_conj
      ((s + ((if χ.Even then 0 else 1 : ℝ) : ℂ)) / 2)
  have hpi : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) :=
    (Complex.ofReal_log Real.pi_pos.le).symm
  rw [hg, hpi]
  simp [Complex.conj_ofNat]

/-- The real right-edge gamma/level integrand is even in its signed height. -/
theorem gammaFactor_level_integrand_even
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (1 / 2 : ℝ) * Real.log (q : ℝ) +
        (logDeriv χ.gammaFactor ((3 / 2 : ℂ) + I * ((-t : ℝ) : ℂ))).re =
      (1 / 2 : ℝ) * Real.log (q : ℝ) +
        (logDeriv χ.gammaFactor ((3 / 2 : ℂ) + I * (t : ℂ))).re := by
  have hpath : (3 / 2 : ℂ) + I * ((-t : ℝ) : ℂ) =
      conj ((3 / 2 : ℂ) + I * (t : ℂ)) := by
    apply Complex.ext <;> norm_num [Complex.conj_ofNat]
  have hre : 0 < ((3 / 2 : ℂ) + I * (t : ℂ)).re := by
    norm_num [Complex.mul_re]
  rw [hpath, gammaFactor_logDeriv_conj q χ _ hre]
  simp

/-- Actual symmetric integration on the right edge, with integrability
supplied by the checked continuity theorem, including the fixed low heights. -/
theorem gammaFactor_level_symmetric_integral
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (∫ t in -T..T, (1 / 2 : ℝ) * Real.log (q : ℝ) +
      (logDeriv χ.gammaFactor ((3 / 2 : ℂ) + I * (t : ℂ))).re) =
    2 * (∫ t in (0 : ℝ)..T, (1 / 2 : ℝ) * Real.log (q : ℝ) +
      (logDeriv χ.gammaFactor ((3 / 2 : ℂ) + I * (t : ℂ))).re) := by
  let F : ℝ → ℝ := fun t => (1 / 2 : ℝ) * Real.log (q : ℝ) +
    (logDeriv χ.gammaFactor ((3 / 2 : ℂ) + I * (t : ℂ))).re
  have hneg : (∫ t in -T..(0 : ℝ), F t) = ∫ t in (0 : ℝ)..T, F t := by
    calc
      (∫ t in -T..(0 : ℝ), F t) = ∫ t in (0 : ℝ)..T, F (-t) := by
        simpa only [neg_zero] using
          (intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := T) F).symm
      _ = ∫ t in (0 : ℝ)..T, F t := by
        apply intervalIntegral.integral_congr
        intro t _
        exact gammaFactor_level_integrand_even q χ t
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (gammaFactor_level_integrand_intervalIntegrable q χ (-T) 0)
    (gammaFactor_level_integrand_intervalIntegrable q χ 0 T)
  change (∫ t in -T..T, F t) = 2 * (∫ t in (0 : ℝ)..T, F t)
  change (∫ t in -T..(0 : ℝ), F t) + (∫ t in (0 : ℝ)..T, F t) =
    (∫ t in -T..T, F t) at hsum
  rw [← hsum, hneg]
  ring

/-- The conductor term cancels exactly at the lower endpoint. The remaining
constant is uniform in the conductor and character, since the actual gamma
factor is one of two fixed functions. No unspecified family bound is assumed. -/
theorem gammaFactor_level_base_error_uniform :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        |(∫ t in (0 : ℝ)..2, (1 / 2 : ℝ) * Real.log (q : ℝ) +
          (logDeriv χ.gammaFactor ((3 / 2 : ℂ) + I * (t : ℂ))).re) -
          Real.log ((q : ℝ) / (Real.pi * Real.exp 1))| ≤ C := by
  classical
  let B₀ : ℝ := (∫ t in (0 : ℝ)..2,
      (logDeriv Complex.Gammaℝ ((3 / 2 : ℂ) + I * (t : ℂ))).re) +
    Real.log (Real.pi * Real.exp 1)
  let B₁ : ℝ := (∫ t in (0 : ℝ)..2,
      (logDeriv (fun z : ℂ => Complex.Gammaℝ (z + 1))
        ((3 / 2 : ℂ) + I * (t : ℂ))).re) +
    Real.log (Real.pi * Real.exp 1)
  refine ⟨|B₀| + |B₁|, add_nonneg (abs_nonneg _) (abs_nonneg _), ?_⟩
  intro q _ χ
  let g : ℝ → ℝ := fun t =>
    (logDeriv χ.gammaFactor ((3 / 2 : ℂ) + I * (t : ℂ))).re
  have hgcont : Continuous g := by
    convert (gammaFactor_level_integrand_continuous q χ).sub
      (continuous_const : Continuous (fun _ : ℝ =>
        (1 / 2 : ℝ) * Real.log (q : ℝ))) using 1
    funext t
    dsimp [g]
    ring
  have hg : IntervalIntegrable g volume 0 2 := hgcont.intervalIntegrable 0 2
  have hc : IntervalIntegrable (fun _ : ℝ =>
      (1 / 2 : ℝ) * Real.log (q : ℝ)) volume 0 2 :=
    (continuous_const : Continuous (fun _ : ℝ =>
      (1 / 2 : ℝ) * Real.log (q : ℝ))).intervalIntegrable 0 2
  have hsplit : (∫ t in (0 : ℝ)..2,
      (1 / 2 : ℝ) * Real.log (q : ℝ) + g t) =
      Real.log (q : ℝ) + ∫ t in (0 : ℝ)..2, g t := by
    rw [intervalIntegral.integral_add hc hg]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hbase : (∫ t in (0 : ℝ)..2,
      (1 / 2 : ℝ) * Real.log (q : ℝ) + g t) -
      Real.log ((q : ℝ) / (Real.pi * Real.exp 1)) =
      (∫ t in (0 : ℝ)..2, g t) + Real.log (Real.pi * Real.exp 1) := by
    rw [hsplit, Real.log_div hq (mul_ne_zero Real.pi_ne_zero (Real.exp_ne_zero 1))]
    ring
  change |(∫ t in (0 : ℝ)..2,
    (1 / 2 : ℝ) * Real.log (q : ℝ) + g t) -
    Real.log ((q : ℝ) / (Real.pi * Real.exp 1))| ≤ |B₀| + |B₁|
  rw [hbase]
  by_cases he : χ.Even
  · have hf : χ.gammaFactor = Complex.Gammaℝ :=
      funext (fun z => he.gammaFactor_def z)
    change |(∫ t in (0 : ℝ)..2,
        (logDeriv χ.gammaFactor ((3 / 2 : ℂ) + I * (t : ℂ))).re) +
      Real.log (Real.pi * Real.exp 1)| ≤ |B₀| + |B₁|
    rw [hf]
    exact le_add_of_nonneg_right (abs_nonneg B₁)
  · have hf : χ.gammaFactor = (fun z : ℂ => Complex.Gammaℝ (z + 1)) := by
      funext z
      simp only [DirichletCharacter.gammaFactor, if_neg he]
    change |(∫ t in (0 : ℝ)..2,
        (logDeriv χ.gammaFactor ((3 / 2 : ℂ) + I * (t : ℂ))).re) +
      Real.log (Real.pi * Real.exp 1)| ≤ |B₀| + |B₁|
    rw [hf]
    exact le_add_of_nonneg_left (abs_nonneg B₀)

/-- The checked positive-height main term extends to the full signed right
edge, with a single absolute fixed-base constant and the explicit upper
error retained. No parity, primitivity, or conductor-one exception occurs. -/
theorem gammaFactor_level_symmetric_main_integral_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
        (T : ℝ), 2 ≤ T →
        |(∫ t in -T..T, (1 / 2 : ℝ) * Real.log (q : ℝ) +
          (logDeriv χ.gammaFactor ((3 / 2 : ℂ) + I * (t : ℂ))).re) -
          T * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| ≤
          6 * (Real.log T - Real.log 2) +
            (25 / 8 : ℝ) * ((1 / 2 : ℝ) - 1 / T) + C := by
  rcases gammaFactor_level_base_error_uniform with ⟨C, hC, hbase⟩
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro q _ χ T hT
  let F : ℝ → ℝ := fun t => (1 / 2 : ℝ) * Real.log (q : ℝ) +
    (logDeriv χ.gammaFactor ((3 / 2 : ℂ) + I * (t : ℂ))).re
  let M : ℝ → ℝ := fun t =>
    (t / 2) * Real.log ((q : ℝ) * t / (2 * Real.pi * Real.exp 1))
  let eH : ℝ := (∫ t in (2 : ℝ)..T, F t) - (M T - M 2)
  let eB : ℝ := (∫ t in (0 : ℝ)..2, F t) - M 2
  have hH : |eH| ≤ 3 * (Real.log T - Real.log 2) +
      (25 / 16 : ℝ) * ((1 / 2 : ℝ) - 1 / T) :=
    gammaFactor_level_main_integral_bound q χ T hT
  have hM₂ : M 2 = Real.log ((q : ℝ) / (Real.pi * Real.exp 1)) := by
    dsimp [M]
    rw [show (2 : ℝ) / 2 = 1 by norm_num, one_mul]
    congr 1
    field_simp [Real.pi_ne_zero, Real.exp_ne_zero]
    <;> ring
  have hB : |eB| ≤ C := by
    dsimp only [eB]
    rw [hM₂]
    exact hbase q χ
  have hsum : (∫ t in (0 : ℝ)..2, F t) + (∫ t in (2 : ℝ)..T, F t) =
      ∫ t in (0 : ℝ)..T, F t :=
    intervalIntegral.integral_add_adjacent_intervals
      (gammaFactor_level_integrand_intervalIntegrable q χ 0 2)
      (gammaFactor_level_integrand_intervalIntegrable q χ 2 T)
  have hsym : (∫ t in -T..T, F t) = 2 * (∫ t in (0 : ℝ)..T, F t) :=
    gammaFactor_level_symmetric_integral q χ T
  have herr : (∫ t in -T..T, F t) -
      T * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) =
      2 * eH + 2 * eB := by
    rw [hsym, ← hsum]
    dsimp [eH, eB, M]
    ring
  change |(∫ t in -T..T, F t) -
    T * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| ≤ _
  rw [herr]
  calc
    |2 * eH + 2 * eB| ≤ |2 * eH| + |2 * eB| := abs_add_le _ _
    _ = 2 * |eH| + 2 * |eB| := by norm_num [abs_mul]
    _ ≤ 2 * (3 * (Real.log T - Real.log 2) +
        (25 / 16 : ℝ) * ((1 / 2 : ℝ) - 1 / T)) + 2 * C :=
      add_le_add (mul_le_mul_of_nonneg_left hH (by norm_num))
        (mul_le_mul_of_nonneg_left hB (by norm_num))
    _ = 6 * (Real.log T - Real.log 2) +
        (25 / 8 : ℝ) * ((1 / 2 : ℝ) - 1 / T) + 2 * C := by ring

/-- An absolute logarithmic error for the actual full gamma/level right
edge, with the constant before every conductor and character. -/
theorem gammaFactor_level_symmetric_main_integral_log_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
        (T : ℝ), 2 ≤ T →
        |(∫ t in -T..T, (1 / 2 : ℝ) * Real.log (q : ℝ) +
          (logDeriv χ.gammaFactor ((3 / 2 : ℂ) + I * (t : ℂ))).re) -
          T * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| ≤
          C * Real.log ((q : ℝ) * T) := by
  rcases gammaFactor_level_symmetric_main_integral_bound with ⟨C, hC, hb⟩
  have hlog₂ : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let K : ℝ := 25 / 16 + C
  have hK : 0 ≤ K := by dsimp [K]; linarith
  refine ⟨6 + K / Real.log 2, by positivity, ?_⟩
  intro q _ χ T hT
  have hqnat : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqnat
  have hTpos : 0 < T := by linarith
  have hTq : T ≤ (q : ℝ) * T := by nlinarith
  have hlogT : Real.log T ≤ Real.log ((q : ℝ) * T) :=
    Real.log_le_log hTpos hTq
  have hlogq : Real.log (2 : ℝ) ≤ Real.log ((q : ℝ) * T) :=
    Real.log_le_log (by norm_num) (hT.trans hTq)
  have hconst : K ≤ K / Real.log 2 * Real.log ((q : ℝ) * T) := by
    calc
      K = K / Real.log 2 * Real.log 2 :=
        (div_mul_cancel₀ K (ne_of_gt hlog₂)).symm
      _ ≤ K / Real.log 2 * Real.log ((q : ℝ) * T) :=
        mul_le_mul_of_nonneg_left hlogq (div_nonneg hK hlog₂.le)
  have hInv : 0 ≤ 1 / T := div_nonneg (by norm_num) hTpos.le
  calc
    |(∫ t in -T..T, (1 / 2 : ℝ) * Real.log (q : ℝ) +
        (logDeriv χ.gammaFactor ((3 / 2 : ℂ) + I * (t : ℂ))).re) -
        T * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| ≤
        6 * (Real.log T - Real.log 2) +
          (25 / 8 : ℝ) * ((1 / 2 : ℝ) - 1 / T) + C := hb q χ T hT
    _ ≤ 6 * Real.log T + K := by dsimp [K]; linarith
    _ ≤ 6 * Real.log ((q : ℝ) * T) +
        K / Real.log 2 * Real.log ((q : ℝ) * T) :=
      add_le_add (mul_le_mul_of_nonneg_left hlogT (by norm_num)) hconst
    _ = (6 + K / Real.log 2) * Real.log ((q : ℝ) * T) := by ring


end RiemannVonMangoldt
end P2MFinalSource050

/- Source module: GammaHorizontalBoundV3
   Original SHA256: e17ebf3f35aba400ff032c26d63c50c86fb905dee89a7b79fc5e94dc6fb17c57 -/
section P2MFinalSource051

open Complex Set MeasureTheory
open scoped Interval
set_option autoImplicit false

namespace RiemannVonMangoldt

/-- The imaginary part of the actual gamma-factor logarithmic derivative
has an absolute bound at either signed height. This uses only the already
checked uniform gamma remainder and the principal logarithm's arg bound. -/
theorem gammaFactor_logDeriv_im_bound
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 0 < s.re) (ht : 3 ≤ |s.im|) :
    |(logDeriv χ.gammaFactor s).im| ≤ Real.pi / 2 + 1 := by
  classical
  let w : ℂ := (s + ((if χ.Even then 0 else 1 : ℝ) : ℂ)) / 2
  let M : ℂ := -Complex.log (Real.pi : ℂ) / 2 + Complex.log w / 2
  have hrem : ‖logDeriv χ.gammaFactor s - M‖ ≤ 3 / |s.im| := by
    simpa only [M, w, logDeriv_apply] using
      gammaFactor_log_derivative_main_term q χ s hs (by linarith)
  have hpi : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) :=
    (Complex.ofReal_log Real.pi_pos.le).symm
  have hM : M.im = Complex.arg w / 2 := by
    simp [M, hpi, Complex.log_im]
  have hmodel : |M.im| ≤ Real.pi / 2 := by
    calc
      |M.im| = |Complex.arg w| / 2 := by rw [hM]; simp [abs_div]
      _ ≤ Real.pi / 2 := div_le_div_of_nonneg_right (Complex.abs_arg_le_pi w) (by norm_num)
  have herr : |(logDeriv χ.gammaFactor s - M).im| ≤ 3 / |s.im| :=
    (Complex.abs_im_le_norm _).trans hrem
  have hdiv : 3 / |s.im| ≤ 1 := (div_le_one (by linarith : 0 < |s.im|)).mpr ht
  have heq : (logDeriv χ.gammaFactor s).im =
      (logDeriv χ.gammaFactor s - M).im + M.im := by simp only [sub_im]; ring
  rw [heq]
  calc
    |(logDeriv χ.gammaFactor s - M).im + M.im| ≤
        |(logDeriv χ.gammaFactor s - M).im| + |M.im| := abs_add_le _ _
    _ ≤ 3 / |s.im| + Real.pi / 2 := add_le_add herr hmodel
    _ ≤ Real.pi / 2 + 1 := by linarith

/-- Actual continuity on the closed unit segment in the positive half-plane
holds at every height, since the genuine gamma factor is analytic and nonzero. -/
theorem gammaFactor_horizontal_logDeriv_continuousOn
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ContinuousOn
      (fun σ : ℝ => logDeriv χ.gammaFactor ((σ : ℂ) + (t : ℂ) * I))
      (uIcc (1 / 2 : ℝ) (3 / 2)) := by
  rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2)]
  intro σ hσ
  have hs : 0 < ((σ : ℂ) + (t : ℂ) * I).re := by
    simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    linarith [hσ.1]
  have hpath : ContinuousAt (fun x : ℝ => (x : ℂ) + (t : ℂ) * I) σ := by fun_prop
  exact ((gammaFactor_logDeriv_continuousAt_of_re_pos q χ _ hs).comp
    (f := fun x : ℝ => (x : ℂ) + (t : ℂ) * I) (x := σ) hpath).continuousWithinAt

/-- The four horizontal gamma contributions in the paired contour formula
are bounded by an absolute constant. Integrability and commuting imaginary
part with the integral are supplied, and the segment has actual length one. -/
theorem gammaFactor_horizontal_logDeriv_integral_bound
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) (ht : 3 ≤ |t|) :
    IntervalIntegrable
      (fun σ : ℝ => logDeriv χ.gammaFactor ((σ : ℂ) + (t : ℂ) * I))
      volume (1 / 2 : ℝ) (3 / 2) ∧
    (∫ σ in (1 / 2 : ℝ)..(3 / 2),
      (logDeriv χ.gammaFactor ((σ : ℂ) + (t : ℂ) * I)).im) =
      (∫ σ in (1 / 2 : ℝ)..(3 / 2),
        logDeriv χ.gammaFactor ((σ : ℂ) + (t : ℂ) * I)).im ∧
    |(∫ σ in (1 / 2 : ℝ)..(3 / 2),
      logDeriv χ.gammaFactor ((σ : ℂ) + (t : ℂ) * I)).im| ≤ Real.pi / 2 + 1 := by
  have hI : IntervalIntegrable
      (fun σ : ℝ => logDeriv χ.gammaFactor ((σ : ℂ) + (t : ℂ) * I))
      volume (1 / 2 : ℝ) (3 / 2) :=
    (gammaFactor_horizontal_logDeriv_continuousOn q χ t).intervalIntegrable
  have hcomm : (∫ σ in (1 / 2 : ℝ)..(3 / 2),
      (logDeriv χ.gammaFactor ((σ : ℂ) + (t : ℂ) * I)).im) =
      (∫ σ in (1 / 2 : ℝ)..(3 / 2),
        logDeriv χ.gammaFactor ((σ : ℂ) + (t : ℂ) * I)).im :=
    intervalIntegral.intervalIntegral_im hI
  refine ⟨hI, hcomm, ?_⟩
  rw [← hcomm]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1 / 2 : ℝ)) (b := (3 / 2 : ℝ)) (C := Real.pi / 2 + 1)
    (f := fun σ : ℝ => (logDeriv χ.gammaFactor ((σ : ℂ) + (t : ℂ) * I)).im) (by
      intro σ hσ
      have hσ' : σ ∈ Icc (1 / 2 : ℝ) (3 / 2) := by
        simpa only [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2)] using
          (uIoc_subset_uIcc hσ)
      have hs : 0 < ((σ : ℂ) + (t : ℂ) * I).re := by
        simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
          mul_zero, zero_mul, sub_zero, add_zero]
        linarith [hσ'.1]
      have hheight : 3 ≤ |((σ : ℂ) + (t : ℂ) * I).im| := by simpa using ht
      simpa only [Real.norm_eq_abs] using
        gammaFactor_logDeriv_im_bound q χ ((σ : ℂ) + (t : ℂ) * I) hs hheight)
  simpa only [Real.norm_eq_abs, show (3 / 2 : ℝ) - 1 / 2 = 1 by norm_num,
    abs_one, mul_one] using hb


end RiemannVonMangoldt
end P2MFinalSource051

/- Source module: GammaContourErrorV6
   Original SHA256: 4425841c4efb39ed266deeb273b7f22931985037d203673941b8be97e97d75c7 -/
section P2MFinalSource052

set_option autoImplicit false
open Complex Set MeasureTheory

namespace RiemannVonMangoldt.Contour

/-- Genuine continuity of the gamma logarithmic derivative on the whole
right edge, including height zero. This is independent of L-function zeros. -/
theorem gammaFactor_rightVertical_continuous
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    Continuous (fun t : ℝ =>
      logDeriv χ.gammaFactor (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hre : 0 < (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I).re := by
    norm_num [Complex.mul_re]
  exact (gammaFactor_logDeriv_continuousAt_of_re_pos q χ _ hre).comp
    (f := fun t : ℝ => ((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) (x := t)
    (by fun_prop : ContinuousAt
      (fun t : ℝ => ((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) t)

/-- The real level/gamma integral is the conductor contribution plus the
real part of the actual complex right-edge integral. Actual integrability
discharges the real-part commutation premise. -/
theorem gammaFactor_rightVertical_level_identity
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (∫ t in -T..T, (1 / 2 : ℝ) * Real.log (q : ℝ) +
      (logDeriv χ.gammaFactor ((3 / 2 : ℂ) + I * (t : ℂ))).re) =
    T * Real.log (q : ℝ) + (rightVertical (logDeriv χ.gammaFactor) T).re := by
  let g : ℝ → ℂ := fun t =>
    logDeriv χ.gammaFactor (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
  have hgcont : Continuous g := gammaFactor_rightVertical_continuous q χ
  have hg : IntervalIntegrable g volume (-T) T := hgcont.intervalIntegrable (-T) T
  have hcomm : (∫ t in -T..T, (g t).re) = (∫ t in -T..T, g t).re :=
    intervalIntegral.intervalIntegral_re hg
  have hgre : IntervalIntegrable (fun t : ℝ => (g t).re) volume (-T) T :=
    (Complex.continuous_re.comp hgcont).intervalIntegrable (-T) T
  have hc : IntervalIntegrable (fun _ : ℝ =>
      (1 / 2 : ℝ) * Real.log (q : ℝ)) volume (-T) T :=
    (continuous_const : Continuous (fun _ : ℝ =>
      (1 / 2 : ℝ) * Real.log (q : ℝ))).intervalIntegrable (-T) T
  calc
    (∫ t in -T..T, (1 / 2 : ℝ) * Real.log (q : ℝ) +
        (logDeriv χ.gammaFactor ((3 / 2 : ℂ) + I * (t : ℂ))).re) =
        ∫ t in -T..T, (1 / 2 : ℝ) * Real.log (q : ℝ) + (g t).re := by
      apply intervalIntegral.integral_congr
      intro t _
      simp only [g, Complex.ofReal_div, Complex.ofReal_ofNat, mul_comm I]
    _ = (∫ _t in -T..T, (1 / 2 : ℝ) * Real.log (q : ℝ)) +
        ∫ t in -T..T, (g t).re := intervalIntegral.integral_add hc hgre
    _ = T * Real.log (q : ℝ) + (rightVertical (logDeriv χ.gammaFactor) T).re := by
      rw [intervalIntegral.integral_const, hcomm]
      change (T - -T) • ((1 / 2 : ℝ) * Real.log (q : ℝ)) +
        (rightVertical (logDeriv χ.gammaFactor) T).re = _
      simp only [smul_eq_mul]
      ring

/-- The exact gamma-and-conductor expression in the paired contour formula
has the required main term and an absolute logarithmic error. The two
characters remain distinct, and all four signed horizontal edges are kept. -/
theorem gamma_contour_error_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
        (T : ℝ), 3 ≤ T →
        |2 * T * Real.log (q : ℝ) +
          ((rightVertical (logDeriv χ.gammaFactor) T).re +
            (rightVertical (logDeriv (χ⁻¹).gammaFactor) T).re) +
          ((horizontal (logDeriv χ.gammaFactor) (-T)).im +
            (horizontal (logDeriv (χ⁻¹).gammaFactor) (-T)).im -
            (horizontal (logDeriv χ.gammaFactor) T).im -
            (horizontal (logDeriv (χ⁻¹).gammaFactor) T).im) -
          2 * T * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| ≤
          C * Real.log ((q : ℝ) * T) := by
  rcases gammaFactor_level_symmetric_main_integral_log_bound with ⟨C, hC, hv⟩
  let A : ℝ := Real.pi / 2 + 1
  let K : ℝ := 4 * A
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK : 0 ≤ K := mul_nonneg (by norm_num) hA
  have hlog₂ : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨2 * C + K / Real.log 2, by positivity, ?_⟩
  intro q _ χ T hT
  let M : ℝ := T * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))
  let eχ : ℝ := T * Real.log (q : ℝ) +
    (rightVertical (logDeriv χ.gammaFactor) T).re - M
  let eι : ℝ := T * Real.log (q : ℝ) +
    (rightVertical (logDeriv (χ⁻¹).gammaFactor) T).re - M
  let H : ℝ := (horizontal (logDeriv χ.gammaFactor) (-T)).im +
    (horizontal (logDeriv (χ⁻¹).gammaFactor) (-T)).im -
    (horizontal (logDeriv χ.gammaFactor) T).im -
    (horizontal (logDeriv (χ⁻¹).gammaFactor) T).im
  have heχ : |eχ| ≤ C * Real.log ((q : ℝ) * T) := by
    have h := hv q χ T (by linarith)
    rw [gammaFactor_rightVertical_level_identity q χ T] at h
    exact h
  have heι : |eι| ≤ C * Real.log ((q : ℝ) * T) := by
    have h := hv q (χ⁻¹) T (by linarith)
    rw [gammaFactor_rightVertical_level_identity q (χ⁻¹) T] at h
    exact h
  have hTpos : 0 < T := by linarith
  have hp : 3 ≤ |T| := by simpa only [abs_of_pos hTpos] using hT
  have hn : 3 ≤ |-T| := by simpa only [abs_neg] using hp
  have hχp : |(horizontal (logDeriv χ.gammaFactor) T).im| ≤ A :=
    (gammaFactor_horizontal_logDeriv_integral_bound q χ T hp).2.2
  have hχn : |(horizontal (logDeriv χ.gammaFactor) (-T)).im| ≤ A :=
    (gammaFactor_horizontal_logDeriv_integral_bound q χ (-T) hn).2.2
  have hιp : |(horizontal (logDeriv (χ⁻¹).gammaFactor) T).im| ≤ A :=
    (gammaFactor_horizontal_logDeriv_integral_bound q (χ⁻¹) T hp).2.2
  have hιn : |(horizontal (logDeriv (χ⁻¹).gammaFactor) (-T)).im| ≤ A :=
    (gammaFactor_horizontal_logDeriv_integral_bound q (χ⁻¹) (-T) hn).2.2
  have hH : |H| ≤ K := by
    rcases abs_le.mp hχp with ⟨hχpl, hχpu⟩
    rcases abs_le.mp hχn with ⟨hχnl, hχnu⟩
    rcases abs_le.mp hιp with ⟨hιpl, hιpu⟩
    rcases abs_le.mp hιn with ⟨hιnl, hιnu⟩
    apply abs_le.mpr
    dsimp [H, K]
    constructor <;> linarith
  have hqnat : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqnat
  have hTq : T ≤ (q : ℝ) * T := by nlinarith
  have hlogq : Real.log (2 : ℝ) ≤ Real.log ((q : ℝ) * T) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hconst : K ≤ K / Real.log 2 * Real.log ((q : ℝ) * T) := by
    calc
      K = K / Real.log 2 * Real.log 2 :=
        (div_mul_cancel₀ K (ne_of_gt hlog₂)).symm
      _ ≤ K / Real.log 2 * Real.log ((q : ℝ) * T) :=
        mul_le_mul_of_nonneg_left hlogq (div_nonneg hK hlog₂.le)
  have herr : 2 * T * Real.log (q : ℝ) +
      ((rightVertical (logDeriv χ.gammaFactor) T).re +
        (rightVertical (logDeriv (χ⁻¹).gammaFactor) T).re) + H -
      2 * T * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) =
      (eχ + eι) + H := by
    dsimp [eχ, eι, M]
    ring
  change |2 * T * Real.log (q : ℝ) +
    ((rightVertical (logDeriv χ.gammaFactor) T).re +
      (rightVertical (logDeriv (χ⁻¹).gammaFactor) T).re) + H -
    2 * T * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| ≤ _
  rw [herr]
  calc
    |(eχ + eι) + H| ≤ |eχ + eι| + |H| := abs_add_le _ _
    _ ≤ (|eχ| + |eι|) + K := add_le_add (abs_add_le _ _) hH
    _ ≤ (C * Real.log ((q : ℝ) * T) + C * Real.log ((q : ℝ) * T)) + K :=
      add_le_add (add_le_add heχ heι) le_rfl
    _ ≤ (C * Real.log ((q : ℝ) * T) + C * Real.log ((q : ℝ) * T)) +
        K / Real.log 2 * Real.log ((q : ℝ) * T) := add_le_add le_rfl hconst
    _ = (2 * C + K / Real.log 2) * Real.log ((q : ℝ) * T) := by ring


end RiemannVonMangoldt.Contour
end P2MFinalSource052

/- Source module: DirichletGoodHeightCountV5
   Original SHA256: 7040c92dedf07d0764f0105231fd298dfa38f6507ae1a21f4f310e3edad8f41b -/
section P2MFinalSource053

/-!
The original Dirichlet zero-count estimate at actual paired good heights.
The count is the unchanged public definition. The absolute constant is
chosen before the conductor, primitive character and height. The principal
two-pole correction is retained and absorbed uniformly into log(q*T).
-/

set_option autoImplicit false

open Complex Set

namespace RiemannVonMangoldt.CountBridge

open Contour RectKernel

/-- One absolute logarithmic error for the unchanged original zero count,
at every height satisfying the four signed nonvanishing conditions. -/
theorem dirichletZeroCount_good_height_error_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
      (hp : chi.IsPrimitive) (T : ℝ), 3 ≤ T →
      (∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2),
        chi.LFunction ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      (∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2),
        chi.LFunction ((x : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0) →
      (∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2),
        (chi⁻¹).LFunction ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      (∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2),
        (chi⁻¹).LFunction ((x : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0) →
      |dirichletZeroCount chi T -
        (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| ≤
        C * Real.log ((q : ℝ) * T) := by
  classical
  obtain ⟨CL, hCL, hL⟩ := paired_L_contour_error_log_uniform
  obtain ⟨CG, hCG, hG⟩ := gamma_contour_error_bound
  have hpi : 0 < 2 * Real.pi := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  refine ⟨(CL + CG) / (2 * Real.pi) + 2 / Real.log 2, by positivity, ?_⟩
  intro q _ chi hp T hT hchipos hchineg hipos hineg
  have hTpos : 0 < T := by linarith
  let p : ℝ := if chi = 1 then 2 else 0
  let M : ℝ := (T / Real.pi) *
    Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))
  let EL : ℝ :=
    ((rightVertical (logDeriv chi.LFunction) T).re +
      (rightVertical (logDeriv (chi⁻¹).LFunction) T).re) +
    ((horizontal (logDeriv chi.LFunction) (-T)).im +
      (horizontal (logDeriv (chi⁻¹).LFunction) (-T)).im -
      (horizontal (logDeriv chi.LFunction) T).im -
      (horizontal (logDeriv (chi⁻¹).LFunction) T).im)
  let EG : ℝ := 2 * T * Real.log (q : ℝ) +
    ((rightVertical (logDeriv chi.gammaFactor) T).re +
      (rightVertical (logDeriv (chi⁻¹).gammaFactor) T).re) +
    ((horizontal (logDeriv chi.gammaFactor) (-T)).im +
      (horizontal (logDeriv (chi⁻¹).gammaFactor) (-T)).im -
      (horizontal (logDeriv chi.gammaFactor) T).im -
      (horizontal (logDeriv (chi⁻¹).gammaFactor) T).im) -
    2 * T * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))
  have hEL : |EL| ≤ CL * Real.log ((q : ℝ) * T) :=
    hL q chi hp T hT hchipos hchineg hipos hineg
  have hEG : |EG| ≤ CG * Real.log ((q : ℝ) * T) := hG q chi T hT
  have hcount := (primitive_completedLFunction_boundary_count_of_paired_good_heights
    chi hp T hTpos hchipos hchineg hipos hineg).2
  have hBcount :
      (boundary (-1 / 2) (3 / 2) (-T) T (logDeriv chi.completedLFunction)).im =
        2 * Real.pi * (dirichletZeroCount chi T - p) := by
    have hi := congrArg Complex.im hcount
    by_cases hchi : chi = 1
    · simpa [p, hchi, mul_im, mul_re] using hi
    · simpa [p, hchi, mul_im, mul_re] using hi
  have hdecomp := primitive_completed_boundary_im_L_gamma chi hp T hTpos
    hchipos hchineg hipos hineg
  have hrel := hBcount.symm.trans hdecomp
  have he : 2 * Real.pi * (dirichletZeroCount chi T - p) -
      2 * T * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) = EL + EG := by
    dsimp [EL, EG]
    linear_combination hrel
  have hraw :
      |2 * Real.pi * (dirichletZeroCount chi T - p) -
        2 * T * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| ≤
      (CL + CG) * Real.log ((q : ℝ) * T) := by
    rw [he]
    calc
      |EL + EG| ≤ |EL| + |EG| := abs_add_le _ _
      _ ≤ CL * Real.log ((q : ℝ) * T) + CG * Real.log ((q : ℝ) * T) :=
        add_le_add hEL hEG
      _ = _ := by ring
  have halg : 2 * Real.pi * (dirichletZeroCount chi T - M - p) =
      2 * Real.pi * (dirichletZeroCount chi T - p) -
        2 * T * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) := by
    dsimp [M]
    field_simp [Real.pi_ne_zero]
    <;> ring
  have hscaled : |dirichletZeroCount chi T - M - p| ≤
      ((CL + CG) / (2 * Real.pi)) * Real.log ((q : ℝ) * T) := by
    apply (mul_le_mul_iff_right₀ hpi).mp
    calc
      (2 * Real.pi) * |dirichletZeroCount chi T - M - p| =
          |2 * Real.pi * (dirichletZeroCount chi T - M - p)| := by
        rw [abs_mul, abs_of_pos hpi]
      _ = |2 * Real.pi * (dirichletZeroCount chi T - p) -
          2 * T * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| := by rw [halg]
      _ ≤ (CL + CG) * Real.log ((q : ℝ) * T) := hraw
      _ = (2 * Real.pi) *
          (((CL + CG) / (2 * Real.pi)) * Real.log ((q : ℝ) * T)) := by
        field_simp [Real.pi_ne_zero]
        <;> ring
  have hpabs : |p| ≤ 2 := by
    dsimp [p]
    split_ifs <;> norm_num
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqt : T ≤ (q : ℝ) * T := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hq hTpos.le
  have hl : Real.log 2 ≤ Real.log ((q : ℝ) * T) :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith)
  have htwo : 2 ≤ (2 / Real.log 2) * Real.log ((q : ℝ) * T) := by
    calc
      2 = (2 / Real.log 2) * Real.log 2 := by field_simp [ne_of_gt hl2]
      _ ≤ (2 / Real.log 2) * Real.log ((q : ℝ) * T) :=
        mul_le_mul_of_nonneg_left hl (by positivity)
  change |dirichletZeroCount chi T - M| ≤ _
  calc
    |dirichletZeroCount chi T - M| ≤
        |dirichletZeroCount chi T - M - p| + |p| := by
      simpa only [sub_add_cancel] using
        abs_add_le (dirichletZeroCount chi T - M - p) p
    _ ≤ ((CL + CG) / (2 * Real.pi)) * Real.log ((q : ℝ) * T) + 2 :=
      add_le_add hscaled hpabs
    _ ≤ ((CL + CG) / (2 * Real.pi)) * Real.log ((q : ℝ) * T) +
        (2 / Real.log 2) * Real.log ((q : ℝ) * T) := add_le_add (le_refl _) htwo
    _ = ((CL + CG) / (2 * Real.pi) + 2 / Real.log 2) *
        Real.log ((q : ℝ) * T) := by ring

end RiemannVonMangoldt.CountBridge

end P2MFinalSource053

/- Source module: UnitHeightPublicV3
   Original SHA256: 0e9762cce428d0aad4994dd2ff40b695a80c44710feda2524d4b40f1c3d8256b -/
section P2MFinalSource054

/-! P2M-16C integrated public-definition proof candidate.

The count is imported from its genuine published module. The support, shell
and monotonicity proofs retain their checked mathematical bodies. The actual
accepted Helfgott supplier discharges the intermediate band premise. -/

set_option autoImplicit false

open Complex Metric Filter Set
open scoped Topology

namespace RiemannVonMangoldt

/-- Analytic orders with the convention that infinite order contributes zero
have finite nonzero weight support on each compact closed ball. -/
private theorem finite_analytic_order_weight_support (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (R : ℝ) :
    (closedBall (0 : ℂ) R ∩
      Function.support (fun s : ℂ => (analyticOrderNatAt f s : ℝ))).Finite := by
  have hfinite :
      (MeromorphicOn.divisor f (closedBall (0 : ℂ) R)).support.Finite :=
    (MeromorphicOn.divisor f (closedBall (0 : ℂ) R)).finiteSupport
      (isCompact_closedBall (0 : ℂ) R)
  apply hfinite.subset
  rintro s ⟨hs, hw⟩
  have ha : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R) :=
    fun z _ => hf.analyticAt z
  rw [Function.mem_support] at hw ⊢
  rw [MeromorphicOn.divisor_apply ha.meromorphicOn hs,
    (ha s hs).meromorphicOrderAt_eq]
  cases ho : analyticOrderAt f s with
  | top =>
    simp [analyticOrderNatAt, ho] at hw
  | coe n =>
    simpa [analyticOrderNatAt, ho] using hw

private theorem in_closedBall_of_strip_height (s : ℂ) (U : ℝ)
    (hre0 : 0 < s.re) (hre1 : s.re < 1) (him : |s.im| ≤ U) :
    s ∈ closedBall (0 : ℂ) (|U| + 2) := by
  have hRe : |s.re| ≤ 1 := by
    rw [abs_of_pos hre0]
    exact le_of_lt hre1
  have hIm : |s.im| ≤ |U| := le_trans him (le_abs_self U)
  rw [mem_closedBall, dist_zero_right]
  calc
    ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    _ ≤ 1 + |U| := add_le_add hRe hIm
    _ ≤ |U| + 2 := by linarith

/-- Exact support required by the platform's Dirichlet zero count, with
both signs of the imaginary part, closed height cutoff, no primitivity
restriction, and no finite-support assumption. -/
theorem dirichlet_weighted_zero_support_finite
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (U : ℝ) :
    ({s : ℂ | 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ U ∧ χ.LFunction s = 0} ∩
      Function.support (fun s : ℂ => (analyticOrderNatAt χ.LFunction s : ℝ))).Finite := by
  by_cases hχ : χ = 1
  · subst χ
    have hfin := finite_analytic_order_weight_support
      (DirichletCharacter.LFunctionTrivChar₁ q)
      (DirichletCharacter.differentiable_LFunctionTrivChar₁ q) (|U| + 2)
    apply hfin.subset
    rintro s ⟨⟨h0, h1, hU, hz⟩, hw⟩
    have hs1 : s ≠ (1 : ℂ) := by
      intro hs
      subst s
      norm_num at h1
    have hAna :
        AnalyticAt ℂ ((1 : DirichletCharacter ℂ q).LFunction) s := by
      have hOpen : IsOpen ({(1 : ℂ)}ᶜ) := isOpen_compl_singleton
      have hDiff : DifferentiableOn ℂ ((1 : DirichletCharacter ℂ q).LFunction)
          ({(1 : ℂ)}ᶜ) := by
        intro z hz'
        have hz1 : z ≠ (1 : ℂ) := by simpa using hz'
        exact (DirichletCharacter.differentiableAt_LFunction _ z
          (Or.inl hz1)).differentiableWithinAt
      exact hDiff.analyticAt (hOpen.mem_nhds (by simpa using hs1))
    have hNear :
        DirichletCharacter.LFunctionTrivChar₁ q =ᶠ[𝓝 s]
          (fun z : ℂ => (z - 1) * (1 : DirichletCharacter ℂ q).LFunction z) := by
      have hnbhd : ({(1 : ℂ)}ᶜ : Set ℂ) ∈ 𝓝 s :=
        isOpen_compl_singleton.mem_nhds (by simpa using hs1)
      filter_upwards [hnbhd] with z hz1
      have hne : z ≠ (1 : ℂ) := by simpa using hz1
      simp [DirichletCharacter.LFunctionTrivChar₁,
        DirichletCharacter.LFunctionTrivChar, hne]
    have hOrder :
        analyticOrderAt (DirichletCharacter.LFunctionTrivChar₁ q) s =
          analyticOrderAt ((1 : DirichletCharacter ℂ q).LFunction) s := by
      calc
        _ = analyticOrderAt
            (fun z : ℂ => (z - 1) * (1 : DirichletCharacter ℂ q).LFunction z) s :=
              analyticOrderAt_congr hNear
        _ = analyticOrderAt (fun z : ℂ => z - 1) s +
            analyticOrderAt ((1 : DirichletCharacter ℂ q).LFunction) s :=
              analyticOrderAt_mul (by fun_prop) hAna
        _ = _ := by simp [analyticOrderAt_id_sub_const_of_ne hs1]
    have hWeight :
        analyticOrderNatAt (DirichletCharacter.LFunctionTrivChar₁ q) s =
          analyticOrderNatAt ((1 : DirichletCharacter ℂ q).LFunction) s := by
      simpa only [analyticOrderNatAt] using congrArg ENat.toNat hOrder
    refine ⟨in_closedBall_of_strip_height s U h0 h1 hU, ?_⟩
    change (analyticOrderNatAt (DirichletCharacter.LFunctionTrivChar₁ q) s : ℝ) ≠ 0
    rw [hWeight]
    exact hw
  · have hfin := finite_analytic_order_weight_support
      χ.LFunction (DirichletCharacter.differentiable_LFunction hχ) (|U| + 2)
    apply hfin.subset
    rintro s ⟨⟨h0, h1, hU, hz⟩, hw⟩
    exact ⟨in_closedBall_of_strip_height s U h0 h1 hU, hw⟩


private def stripZeroSet {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) : Set ℂ :=
  {s | 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧ χ.LFunction s = 0}

private noncomputable def zeroWeight {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ℂ → ℝ :=
  fun s => (analyticOrderNatAt χ.LFunction s : ℝ)

/-- The algebraic finite-support shell subtraction needed before using the
accepted Helfgott unit-band bound. Finiteness remains an explicit premise. -/
theorem finsum_shell_sub {α : Type*} (f : α → ℝ)
    {A B : Set α} (hAB : A ⊆ B)
    (hfin : (B ∩ Function.support f).Finite) :
    (∑ᶠ x ∈ B, f x) - (∑ᶠ x ∈ A, f x) =
      ∑ᶠ x ∈ B \ A, f x := by
  have h := finsum_mem_add_sdiff' (f := f) hAB hfin
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using h.symm)

/-- Exact unconditional strict-left, closed-right signed-height shell of the
original platform zero-count definition, using the kernel-checked finite support theorem. -/
theorem dirichlet_zero_count_sub_eq_signed_shell
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (T U : ℝ) (hTU : T ≤ U) :
    dirichletZeroCount χ U - dirichletZeroCount χ T =
      ∑ᶠ s ∈ {s : ℂ | 0 < s.re ∧ s.re < 1 ∧
           T < |s.im| ∧ |s.im| ≤ U ∧ χ.LFunction s = 0},
         (analyticOrderNatAt χ.LFunction s : ℝ) := by
  have hfinite : (stripZeroSet χ U ∩
      Function.support (zeroWeight χ)).Finite := by
    change ({s : ℂ | 0 < s.re ∧ s.re < 1 ∧
       |s.im| ≤ U ∧ χ.LFunction s = 0} ∩
       Function.support (fun s : ℂ =>
         (analyticOrderNatAt χ.LFunction s : ℝ))).Finite
    exact dirichlet_weighted_zero_support_finite q χ U
  have hsub : stripZeroSet χ T ⊆ stripZeroSet χ U := by
    intro s hs
    rcases hs with ⟨h0, h1, h2, h3⟩
    exact ⟨h0, h1, le_trans h2 hTU, h3⟩
  have h := finsum_shell_sub (zeroWeight χ) hsub hfinite
  have hset : (stripZeroSet χ U) \ (stripZeroSet χ T) =
      {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ T < |s.im| ∧ |s.im| ≤ U ∧
        χ.LFunction s = 0} := by
    ext s
    simp only [stripZeroSet, Set.mem_diff, Set.mem_setOf_eq]
    constructor
    · intro ⟨⟨h0, h1, hU, hz⟩, hn⟩
      have hT : T < |s.im| := by
        by_contra h
        exact hn ⟨h0, h1, le_of_not_gt h, hz⟩
      exact ⟨h0, h1, hT, hU, hz⟩
    · intro ⟨h0, h1, hT, hU, hz⟩
      refine ⟨⟨h0, h1, hU, hz⟩, ?_⟩
      intro hsmall
      exact (not_le_of_gt hT) hsmall.2.2.1
  rw [hset] at h
  simpa only [dirichletZeroCount, stripZeroSet, zeroWeight] using h



/-- Unconditional monotonicity of the original signed Dirichlet zero count,
for arbitrary real heights and all characters, by nonnegative multiplicities. -/
theorem dirichlet_zero_count_mono (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) {T U : ℝ} (hTU : T ≤ U) :
    dirichletZeroCount χ T ≤ dirichletZeroCount χ U := by
  apply sub_nonneg.mp
  rw [dirichlet_zero_count_sub_eq_signed_shell q χ T U hTU]
  apply finsum_nonneg
  intro s
  apply finsum_nonneg
  intro hs
  exact Nat.cast_nonneg _



end RiemannVonMangoldt
end P2MFinalSource054

/- Source module: DirichletGoodHeightExistenceV1
   Original SHA256: ecba068b54903029c4544df7d4b63f1a58c9b3309ae348664a985c58f2b0c6fc -/
section P2MFinalSource055

open Complex Set Filter
open scoped Topology
set_option autoImplicit false

namespace RiemannVonMangoldt.CountBridge

/-- A supplied genuine nonzero point suffices for zero finiteness and finite
orders on a compact rectangle. No boundary nonvanishing is assumed. -/
theorem rectangle_zero_set_finite_and_orders_of_witness
    (a b c d : ℝ) {f : ℂ → ℂ} {w : ℂ}
    (hf : AnalyticOnNhd ℂ f (Icc a b ×ℂ Icc c d))
    (hw : w ∈ (Icc a b ×ℂ Icc c d)) (hfw : f w ≠ 0) :
    {z : ℂ | z ∈ (Icc a b ×ℂ Icc c d) ∧ f z = 0}.Finite ∧
      (∀ z ∈ (Icc a b ×ℂ Icc c d), analyticOrderAt f z ≠ ⊤) := by
  have hpre := RectangleZeros.closed_rectangle_isPreconnected a b c d
  have hconnected : IsConnected (Icc a b ×ℂ Icc c d) := ⟨⟨w, hw⟩, hpre⟩
  have hcompact : IsCompact (Icc a b ×ℂ Icc c d) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hcodiscrete : f ⁻¹' ({0} : Set ℂ)ᶜ ∈ codiscreteWithin (Icc a b ×ℂ Icc c d) :=
    hf.preimage_zero_mem_codiscreteWithin hfw hw hconnected
  have hfinite_diff := hcompact.finite_sdiff_of_mem_codiscreteWithin hcodiscrete
  have hfinite : {z : ℂ | z ∈ (Icc a b ×ℂ Icc c d) ∧ f z = 0}.Finite := by
    apply hfinite_diff.subset
    intro z hz
    exact ⟨hz.1, fun h => h hz.2⟩
  have hw_order : analyticOrderAt f w ≠ ⊤ := by
    rw [(hf w hw).analyticOrderAt_eq_zero.mpr hfw]
    exact ENat.zero_ne_top
  refine ⟨hfinite, ?_⟩
  intro z hz
  exact hf.analyticOrderAt_ne_top_of_isPreconnected hpre hw hz hw_order

/-- Ordinary `L` has finitely many zeros on either signed compact slab away
from the real axis. Its actual nonzero right corner rules out an identically
zero function. This holds for every character, including the principal one. -/
theorem LFunction_zeros_finite_signed_rectangle
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (c d : ℝ) (hcd : c ≤ d) (hsign : 0 < c ∨ d < 0) :
    {z : ℂ | z ∈ (Icc (1 / 2 : ℝ) (3 / 2) ×ℂ Icc c d) ∧
      χ.LFunction z = 0}.Finite := by
  have hf : AnalyticOnNhd ℂ χ.LFunction
      (Icc (1 / 2 : ℝ) (3 / 2) ×ℂ Icc c d) := by
    intro z hz
    have hz1 : z ≠ 1 := by
      intro h
      have hi : z.im = 0 := by simpa only [one_im] using congrArg Complex.im h
      rcases hsign with hc | hd
      · linarith [hz.2.1]
      · linarith [hz.2.2]
    apply analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [eventually_ne_nhds hz1] with s hs
    exact χ.differentiableAt_LFunction s (.inl hs)
  let w : ℂ := ((3 / 2 : ℝ) : ℂ) + (c : ℂ) * I
  have hw : w ∈ (Icc (1 / 2 : ℝ) (3 / 2) ×ℂ Icc c d) := by
    norm_num [w, mem_reProdIm, hcd]
  have hw1 : w ≠ 1 := by
    intro h
    have he := congrArg Complex.re h
    norm_num [w] at he
  have hfw : χ.LFunction w ≠ 0 :=
    χ.LFunction_ne_zero_of_one_le_re (.inr hw1) (by norm_num [w])
  exact (rectangle_zero_set_finite_and_orders_of_witness
    (1 / 2) (3 / 2) c d hf hw hfw).1

/-- Every positive open height interval contains a common good height for
`χ` and `χ⁻¹` at both signs. The proof excludes a genuinely finite set of
zero heights on the two signed compact slabs; no separation bound, zero
count, or pre-existing good contour is assumed. -/
theorem exists_paired_good_height_between
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ t : ℝ, a < t ∧ t < b ∧
      (∀ σ ∈ Icc (1 / 2 : ℝ) (3 / 2),
        χ.LFunction ((σ : ℂ) + (t : ℂ) * I) ≠ 0) ∧
      (∀ σ ∈ Icc (1 / 2 : ℝ) (3 / 2),
        χ.LFunction ((σ : ℂ) + ((-t : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ σ ∈ Icc (1 / 2 : ℝ) (3 / 2),
        (χ⁻¹).LFunction ((σ : ℂ) + (t : ℂ) * I) ≠ 0) ∧
      (∀ σ ∈ Icc (1 / 2 : ℝ) (3 / 2),
        (χ⁻¹).LFunction ((σ : ℂ) + ((-t : ℝ) : ℂ) * I) ≠ 0) := by
  let Zp : DirichletCharacter ℂ q → Set ℂ := fun ψ =>
    {z | z ∈ (Icc (1 / 2 : ℝ) (3 / 2) ×ℂ Icc a b) ∧ ψ.LFunction z = 0}
  let Zn : DirichletCharacter ℂ q → Set ℂ := fun ψ =>
    {z | z ∈ (Icc (1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-b) (-a)) ∧ ψ.LFunction z = 0}
  have hp (ψ : DirichletCharacter ℂ q) : (Zp ψ).Finite :=
    LFunction_zeros_finite_signed_rectangle ψ a b hab.le (.inl ha)
  have hn (ψ : DirichletCharacter ℂ q) : (Zn ψ).Finite :=
    LFunction_zeros_finite_signed_rectangle ψ (-b) (-a)
      (by linarith) (.inr (by linarith))
  let Z : Set ℂ := ((Zp χ ∪ Zn χ) ∪ Zp (χ⁻¹)) ∪ Zn (χ⁻¹)
  have hZ : Z.Finite := ((hp χ |>.union (hn χ)).union (hp (χ⁻¹))).union (hn (χ⁻¹))
  let Bad : Set ℝ := (fun z : ℂ => |z.im|) '' Z
  have hBad : Bad.Finite := hZ.image _
  obtain ⟨t, ht, htnot⟩ := (Set.Ioo_infinite hab).exists_notMem_finite hBad
  have htpos : 0 < t := ha.trans ht.1
  have hgood (ψ : DirichletCharacter ℂ q) (hup : Zp ψ ⊆ Z) (hdn : Zn ψ ⊆ Z) :
      (∀ σ ∈ Icc (1 / 2 : ℝ) (3 / 2),
        ψ.LFunction ((σ : ℂ) + (t : ℂ) * I) ≠ 0) ∧
      (∀ σ ∈ Icc (1 / 2 : ℝ) (3 / 2),
        ψ.LFunction ((σ : ℂ) + ((-t : ℝ) : ℂ) * I) ≠ 0) := by
    constructor
    · intro σ hσ hz
      apply htnot
      refine ⟨(σ : ℂ) + (t : ℂ) * I, hup ⟨?_, hz⟩, ?_⟩
      · simpa [mem_reProdIm] using
          (show σ ∈ Icc (1 / 2 : ℝ) (3 / 2) ∧ t ∈ Icc a b from
            ⟨hσ, ⟨ht.1.le, ht.2.le⟩⟩)
      · simp [abs_of_pos htpos]
    · intro σ hσ hz
      apply htnot
      refine ⟨(σ : ℂ) + ((-t : ℝ) : ℂ) * I, hdn ⟨?_, hz⟩, ?_⟩
      · have htm : -t ∈ Icc (-b) (-a) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
        simpa [mem_reProdIm] using
          (show σ ∈ Icc (1 / 2 : ℝ) (3 / 2) ∧ -t ∈ Icc (-b) (-a) from ⟨hσ, htm⟩)
      · simp [abs_of_pos htpos]
  obtain ⟨hχpos, hχneg⟩ := hgood χ
    (fun _ hz => .inl (.inl (.inl hz)))
    (fun _ hz => .inl (.inl (.inr hz)))
  obtain ⟨hipos, hineg⟩ := hgood (χ⁻¹)
    (fun _ hz => .inl (.inr hz)) (fun _ hz => .inr hz)
  exact ⟨t, ht.1, ht.2, hχpos, hχneg, hipos, hineg⟩


end RiemannVonMangoldt.CountBridge
end P2MFinalSource055

/- Source module: DirichletEndpointEstimatesV2
   Original SHA256: 0a119207a21aa444b055f79a05322eee76c086579857eb513c51af1627e39cfa -/
section P2MFinalSource056

set_option autoImplicit false
open Set

namespace RiemannVonMangoldt.CountBridge.Endpoint

/- Elementary estimates for the exact original main term. The constants
depend only on fixed real numbers, never on q, the character, or the height. -/

noncomputable def logScale : ℝ := 1 + Real.log 3 / Real.log 2

noncomputable def mainScale : ℝ :=
  (logScale + (|Real.log (2 * Real.pi * Real.exp 1)| + 1) / Real.log 2) / Real.pi

theorem logScale_nonneg : 0 ≤ logScale := by
  have h₂ : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h₃ : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  dsimp [logScale]
  positivity

theorem mainScale_nonneg : 0 ≤ mainScale := by
  have h₂ : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hL := logScale_nonneg
  dsimp [mainScale]
  positivity

private theorem modulus_real_one_le (q : ℕ) [NeZero q] : (1 : ℝ) ≤ (q : ℝ) := by
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))

private theorem log_modulus_height_lower
    (q : ℕ) [NeZero q] (T : ℝ) (hT : 2 ≤ T) :
    Real.log (2 : ℝ) ≤ Real.log ((q : ℝ) * T) := by
  have hq := modulus_real_one_le q
  have hTq : T ≤ (q : ℝ) * T := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hq (by linarith : 0 ≤ T)
  exact Real.log_le_log (by norm_num) (hT.trans hTq)

theorem log_modulus_height_nonneg
    (q : ℕ) [NeZero q] (T : ℝ) (hT : 2 ≤ T) :
    0 ≤ Real.log ((q : ℝ) * T) :=
  (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans
    (log_modulus_height_lower q T hT)

private theorem constant_absorb
    (q : ℕ) [NeZero q] (T : ℝ) (hT : 2 ≤ T) (B : ℝ) (hB : 0 ≤ B) :
    B ≤ B / Real.log 2 * Real.log ((q : ℝ) * T) := by
  have h₂ : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  calc
    B = B / Real.log 2 * Real.log 2 :=
      (div_mul_cancel₀ B (ne_of_gt h₂)).symm
    _ ≤ B / Real.log 2 * Real.log ((q : ℝ) * T) :=
      mul_le_mul_of_nonneg_left (log_modulus_height_lower q T hT)
        (div_nonneg hB h₂.le)

/-- Heights at most three times T have a uniformly comparable logarithm.
This covers both neighboring large heights and the fixed low-height witness. -/
theorem log_height_bound
    (q : ℕ) [NeZero q] (T : ℝ) (hT : 2 ≤ T)
    (x : ℝ) (hx : 1 ≤ x) (hxu : x ≤ 3 * T) :
    Real.log ((q : ℝ) * x) ≤ logScale * Real.log ((q : ℝ) * T) := by
  have hq := modulus_real_one_le q
  have hqpos : 0 < (q : ℝ) := by linarith
  have hxpos : 0 < x := by linarith
  have hTpos : 0 < T := by linarith
  have hmul : (q : ℝ) * x ≤ 3 * ((q : ℝ) * T) := by
    calc
      (q : ℝ) * x ≤ (q : ℝ) * (3 * T) :=
        mul_le_mul_of_nonneg_left hxu hqpos.le
      _ = 3 * ((q : ℝ) * T) := by ring
  have hlog := Real.log_le_log (mul_pos hqpos hxpos) hmul
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
    (ne_of_gt (mul_pos hqpos hTpos))] at hlog
  have h₃ := constant_absorb q T hT (Real.log 3)
    (Real.log_pos (by norm_num : (1 : ℝ) < 3)).le
  calc
    Real.log ((q : ℝ) * x) ≤ Real.log 3 + Real.log ((q : ℝ) * T) := hlog
    _ ≤ Real.log 3 / Real.log 2 * Real.log ((q : ℝ) * T) +
        Real.log ((q : ℝ) * T) := by linarith
    _ = logScale * Real.log ((q : ℝ) * T) := by dsimp [logScale]; ring

private theorem model_log_bound
    (q : ℕ) [NeZero q] (T : ℝ) (hT : 2 ≤ T)
    (x : ℝ) (hx : 1 ≤ x) (hxu : x ≤ 3 * T) :
    |Real.log ((q : ℝ) * x / (2 * Real.pi * Real.exp 1))| + 1 ≤
      (logScale + (|Real.log (2 * Real.pi * Real.exp 1)| + 1) / Real.log 2) *
        Real.log ((q : ℝ) * T) := by
  have hq := modulus_real_one_le q
  have hqpos : 0 < (q : ℝ) := by linarith
  have hxpos : 0 < x := by linarith
  have hqx : 1 ≤ (q : ℝ) * x := by
    calc
      (1 : ℝ) ≤ x := hx
      _ ≤ (q : ℝ) * x := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hq hxpos.le
  have hden : (2 : ℝ) * Real.pi * Real.exp 1 ≠ 0 := by positivity
  rw [Real.log_div (ne_of_gt (mul_pos hqpos hxpos)) hden]
  have hc := constant_absorb q T hT
    (|Real.log (2 * Real.pi * Real.exp 1)| + 1) (by positivity)
  calc
    |Real.log ((q : ℝ) * x) - Real.log (2 * Real.pi * Real.exp 1)| + 1 ≤
        |Real.log ((q : ℝ) * x)| + |Real.log (2 * Real.pi * Real.exp 1)| + 1 :=
      by
        have h := abs_sub (Real.log ((q : ℝ) * x))
          (Real.log (2 * Real.pi * Real.exp 1))
        linarith
    _ = Real.log ((q : ℝ) * x) + (|Real.log (2 * Real.pi * Real.exp 1)| + 1) := by
      rw [abs_of_nonneg (Real.log_nonneg hqx)]
      ring
    _ ≤ logScale * Real.log ((q : ℝ) * T) +
        ((|Real.log (2 * Real.pi * Real.exp 1)| + 1) / Real.log 2) *
          Real.log ((q : ℝ) * T) :=
      add_le_add (log_height_bound q T hT x hx hxu) hc
    _ = (logScale + (|Real.log (2 * Real.pi * Real.exp 1)| + 1) / Real.log 2) *
        Real.log ((q : ℝ) * T) := by ring

/-- An absolute bound for the exact main term at every height in [1,5]
used in the low-height bracket. -/
theorem main_abs_bound
    (q : ℕ) [NeZero q] (T : ℝ) (hT : 2 ≤ T)
    (x : ℝ) (hx : 1 ≤ x) (hx5 : x ≤ 5) (hxu : x ≤ 3 * T) :
    |(x / Real.pi) * Real.log ((q : ℝ) * x / (2 * Real.pi * Real.exp 1))| ≤
      5 * mainScale * Real.log ((q : ℝ) * T) := by
  have hxpos : 0 < x := by linarith
  have hp := Real.pi_pos
  have hm := model_log_bound q T hT x hx hxu
  have hE : 0 ≤ logScale + (|Real.log (2 * Real.pi * Real.exp 1)| + 1) / Real.log 2 := by
    have hL := logScale_nonneg
    have h₂ : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hlog := log_modulus_height_nonneg q T hT
  calc
    |(x / Real.pi) * Real.log ((q : ℝ) * x / (2 * Real.pi * Real.exp 1))| =
        (x / Real.pi) * |Real.log ((q : ℝ) * x / (2 * Real.pi * Real.exp 1))| := by
      rw [abs_mul, abs_of_pos (div_pos hxpos hp)]
    _ ≤ (x / Real.pi) * (|Real.log ((q : ℝ) * x / (2 * Real.pi * Real.exp 1))| + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hxpos.le hp.le)
    _ ≤ (x / Real.pi) *
        ((logScale + (|Real.log (2 * Real.pi * Real.exp 1)| + 1) / Real.log 2) *
          Real.log ((q : ℝ) * T)) :=
      mul_le_mul_of_nonneg_left hm (div_nonneg hxpos.le hp.le)
    _ ≤ (5 / Real.pi) *
        ((logScale + (|Real.log (2 * Real.pi * Real.exp 1)| + 1) / Real.log 2) *
          Real.log ((q : ℝ) * T)) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hx5 hp.le) (mul_nonneg hE hlog)
    _ = 5 * mainScale * Real.log ((q : ℝ) * T) := by dsimp [mainScale]; ring

/-- The original main term changes by O(log(qT)) over either neighboring
unit interval. The derivative estimate is proved on the actual positive
interval [T-1,T+1], with no monotonicity assumption on the main term. -/
theorem main_unit_variation
    (q : ℕ) [NeZero q] (T : ℝ) (hT : 4 ≤ T)
    (U : ℝ) (hUl : T - 1 ≤ U) (hUu : U ≤ T + 1) :
    |(U / Real.pi) * Real.log ((q : ℝ) * U / (2 * Real.pi * Real.exp 1)) -
      (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| ≤
      mainScale * Real.log ((q : ℝ) * T) := by
  let f : ℝ → ℝ := fun x => (x / Real.pi) *
    (Real.log (q : ℝ) + Real.log x - Real.log (2 * Real.pi * Real.exp 1))
  let f' : ℝ → ℝ := fun x =>
    (Real.log (q : ℝ) + Real.log x - Real.log (2 * Real.pi * Real.exp 1) + 1) / Real.pi
  have hq := modulus_real_one_le q
  have hqpos : 0 < (q : ℝ) := by linarith
  have hden : (2 : ℝ) * Real.pi * Real.exp 1 ≠ 0 := by positivity
  have hfun (x : ℝ) (hx : 0 < x) : f x =
      (x / Real.pi) * Real.log ((q : ℝ) * x / (2 * Real.pi * Real.exp 1)) := by
    dsimp [f]
    rw [Real.log_div (ne_of_gt (mul_pos hqpos hx)) hden,
      Real.log_mul (ne_of_gt hqpos) (ne_of_gt hx)]
  have hd (x : ℝ) (hx : 0 < x) : HasDerivAt f (f' x) x := by
    have h := ((hasDerivAt_id x).div_const Real.pi).mul
      (((Real.hasDerivAt_log (ne_of_gt hx)).const_add (Real.log (q : ℝ))).sub_const
        (Real.log (2 * Real.pi * Real.exp 1)))
    change HasDerivAt f
      ((1 / Real.pi) * (Real.log (q : ℝ) + Real.log x - Real.log (2 * Real.pi * Real.exp 1)) +
        (x / Real.pi) * x⁻¹) x at h
    convert h using 1
    dsimp [f']
    field_simp [ne_of_gt hx, Real.pi_ne_zero]
    <;> ring
  have hb : ∀ x ∈ Icc (T - 1) (T + 1),
      ‖f' x‖ ≤ mainScale * Real.log ((q : ℝ) * T) := by
    intro x hx
    have hx1 : 1 ≤ x := by linarith [hx.1]
    have hxpos : 0 < x := by linarith
    have hxu : x ≤ 3 * T := by linarith [hx.2]
    have hm := model_log_bound q T (by linarith) x hx1 hxu
    have he : Real.log (q : ℝ) + Real.log x - Real.log (2 * Real.pi * Real.exp 1) =
        Real.log ((q : ℝ) * x / (2 * Real.pi * Real.exp 1)) := by
      rw [Real.log_div (ne_of_gt (mul_pos hqpos hxpos)) hden,
        Real.log_mul (ne_of_gt hqpos) (ne_of_gt hxpos)]
    have htri : |Real.log ((q : ℝ) * x / (2 * Real.pi * Real.exp 1)) + 1| ≤
        |Real.log ((q : ℝ) * x / (2 * Real.pi * Real.exp 1))| + 1 := by
      simpa only [abs_one] using
        (abs_add_le (Real.log ((q : ℝ) * x / (2 * Real.pi * Real.exp 1))) (1 : ℝ))
    dsimp [f']
    rw [abs_div, abs_of_pos Real.pi_pos, he]
    calc
      |Real.log ((q : ℝ) * x / (2 * Real.pi * Real.exp 1)) + 1| / Real.pi ≤
          (|Real.log ((q : ℝ) * x / (2 * Real.pi * Real.exp 1))| + 1) / Real.pi :=
        div_le_div_of_nonneg_right htri Real.pi_pos.le
      _ ≤ ((logScale + (|Real.log (2 * Real.pi * Real.exp 1)| + 1) / Real.log 2) *
          Real.log ((q : ℝ) * T)) / Real.pi :=
        div_le_div_of_nonneg_right hm Real.pi_pos.le
      _ = mainScale * Real.log ((q : ℝ) * T) := by dsimp [mainScale]; ring
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := f')
    (fun x hx => (hd x (by linarith [hx.1])).hasDerivWithinAt) hb
    (convex_Icc (T - 1) (T + 1))
    (show T ∈ Icc (T - 1) (T + 1) from ⟨by linarith, by linarith⟩)
    (show U ∈ Icc (T - 1) (T + 1) from ⟨hUl, hUu⟩)
  have hUpos : 0 < U := by linarith
  have hTpos : 0 < T := by linarith
  have hdist : |U - T| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hmv' :
      |(U / Real.pi) * Real.log ((q : ℝ) * U / (2 * Real.pi * Real.exp 1)) -
        (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| ≤
        (mainScale * Real.log ((q : ℝ) * T)) * |U - T| := by
    simpa only [hfun U hUpos, hfun T hTpos, Real.norm_eq_abs] using hmv
  exact hmv'.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hdist
      (mul_nonneg mainScale_nonneg (log_modulus_height_nonneg q T (by linarith))))


end RiemannVonMangoldt.CountBridge.Endpoint
end P2MFinalSource056

/- Source module: DirichletEndpointTransferV2
   Original SHA256: b14468eb0d8663f65fd5c7f3fe317537727e85feb963009ed901cd364cf173ff -/
section P2MFinalSource057

set_option autoImplicit false
open Complex Set

namespace RiemannVonMangoldt.CountBridge

/- Private parent reduction. The original count and its monotonicity are
imported from the genuine accepted public-definition UnitHeightPublicV3
source. The paired good heights come from the checked finite-zero avoidance
theorem. This file assumes only the remaining uniform good-height estimate
and claims no independent public novelty. -/

/-- A uniform formula at all paired good heights implies the exact original
all-height parent statement. Large T is bracketed by good heights in the two
adjacent unit intervals; 2 ≤ T < 4 is controlled using nonnegativity and one
good height in (4,5). Closed-height zeros are retained by count monotonicity. -/
theorem dirichlet_L_zero_count_of_paired_good_heights
    (hgood :
      ∃ A : ℝ, 0 ≤ A ∧
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
          χ.IsPrimitive → ∀ T : ℝ, 3 ≤ T →
            (∀ σ ∈ Icc (1 / 2 : ℝ) (3 / 2),
              χ.LFunction ((σ : ℂ) + (T : ℂ) * I) ≠ 0) →
            (∀ σ ∈ Icc (1 / 2 : ℝ) (3 / 2),
              χ.LFunction ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0) →
            (∀ σ ∈ Icc (1 / 2 : ℝ) (3 / 2),
              (χ⁻¹).LFunction ((σ : ℂ) + (T : ℂ) * I) ≠ 0) →
            (∀ σ ∈ Icc (1 / 2 : ℝ) (3 / 2),
              (χ⁻¹).LFunction ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0) →
            |dirichletZeroCount χ T -
              T / Real.pi * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| ≤
              A * Real.log ((q : ℝ) * T)) :
    ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → ∀ T : ℝ, 2 ≤ T →
        |dirichletZeroCount χ T -
          T / Real.pi * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| ≤
          C * Real.log ((q : ℝ) * T) := by
  rcases hgood with ⟨A, hA, hgood⟩
  refine ⟨A * Endpoint.logScale + 10 * Endpoint.mainScale, ?_⟩
  intro q _ χ hp T hT
  let N : ℝ → ℝ := dirichletZeroCount χ
  let M : ℝ → ℝ := fun t =>
    t / Real.pi * Real.log ((q : ℝ) * t / (2 * Real.pi * Real.exp 1))
  have hlog : 0 ≤ Real.log ((q : ℝ) * T) := Endpoint.log_modulus_height_nonneg q T hT
  have hD : 0 ≤ Endpoint.mainScale * Real.log ((q : ℝ) * T) :=
    mul_nonneg Endpoint.mainScale_nonneg hlog
  have hAL : 0 ≤ A * Endpoint.logScale * Real.log ((q : ℝ) * T) :=
    mul_nonneg (mul_nonneg hA Endpoint.logScale_nonneg) hlog
  have hheight (U : ℝ) (hU : 1 ≤ U) (hUT : U ≤ 3 * T) :
      A * Real.log ((q : ℝ) * U) ≤
        A * Endpoint.logScale * Real.log ((q : ℝ) * T) := by
    calc
      A * Real.log ((q : ℝ) * U) ≤
          A * (Endpoint.logScale * Real.log ((q : ℝ) * T)) :=
        mul_le_mul_of_nonneg_left (Endpoint.log_height_bound q T hT U hU hUT) hA
      _ = A * Endpoint.logScale * Real.log ((q : ℝ) * T) := by ring
  change |N T - M T| ≤
    (A * Endpoint.logScale + 10 * Endpoint.mainScale) * Real.log ((q : ℝ) * T)
  by_cases hlarge : 4 ≤ T
  · obtain ⟨V, hVl, hVT, hVp, hVn, hiVp, hiVn⟩ :=
      exists_paired_good_height_between χ (T - 1) T (by linarith) (by linarith)
    obtain ⟨U, hTU, hUu, hUp, hUn, hiUp, hiUn⟩ :=
      exists_paired_good_height_between χ T (T + 1) (by linarith) (by linarith)
    have hgv : |N V - M V| ≤ A * Real.log ((q : ℝ) * V) :=
      hgood q χ hp V (by linarith) hVp hVn hiVp hiVn
    have hgu : |N U - M U| ≤ A * Real.log ((q : ℝ) * U) :=
      hgood q χ hp U (by linarith) hUp hUn hiUp hiUn
    have hNV : N V ≤ N T := dirichlet_zero_count_mono q χ hVT.le
    have hNU : N T ≤ N U := dirichlet_zero_count_mono q χ hTU.le
    have hMV : |M V - M T| ≤ Endpoint.mainScale * Real.log ((q : ℝ) * T) :=
      Endpoint.main_unit_variation q T hlarge V hVl.le (by linarith)
    have hMU : |M U - M T| ≤ Endpoint.mainScale * Real.log ((q : ℝ) * T) :=
      Endpoint.main_unit_variation q T hlarge U (by linarith) hUu.le
    have hAV := hheight V (by linarith) (by linarith)
    have hAU := hheight U (by linarith) (by linarith)
    rcases abs_le.mp hgv with ⟨hgvL, hgvU⟩
    rcases abs_le.mp hgu with ⟨hguL, hguU⟩
    rcases abs_le.mp hMV with ⟨hMVL, hMVU⟩
    rcases abs_le.mp hMU with ⟨hMUL, hMUU⟩
    apply abs_le.mpr
    constructor <;> nlinarith
  · obtain ⟨U, h4U, hU5, hUp, hUn, hiUp, hiUn⟩ :=
      exists_paired_good_height_between χ 4 5 (by norm_num) (by norm_num)
    have hgu : |N U - M U| ≤ A * Real.log ((q : ℝ) * U) :=
      hgood q χ hp U (by linarith) hUp hUn hiUp hiUn
    have hNU : N T ≤ N U := dirichlet_zero_count_mono q χ (by linarith)
    have hN0 : 0 ≤ N T := by
      dsimp [N, dirichletZeroCount]
      apply finsum_nonneg
      intro s
      apply finsum_nonneg
      intro hs
      exact Nat.cast_nonneg _
    have hMU : |M U| ≤ 5 * Endpoint.mainScale * Real.log ((q : ℝ) * T) :=
      Endpoint.main_abs_bound q T hT U (by linarith) hU5.le (by linarith)
    have hMT : |M T| ≤ 5 * Endpoint.mainScale * Real.log ((q : ℝ) * T) :=
      Endpoint.main_abs_bound q T hT T (by linarith) (by linarith) (by linarith)
    have hAU := hheight U (by linarith) (by linarith)
    rcases abs_le.mp hgu with ⟨hguL, hguU⟩
    rcases abs_le.mp hMU with ⟨hMUL, hMUU⟩
    rcases abs_le.mp hMT with ⟨hMTL, hMTU⟩
    apply abs_le.mpr
    constructor <;> nlinarith


end RiemannVonMangoldt.CountBridge
end P2MFinalSource057

/- Source module: DirichletLZeroCountV6
   Original SHA256: 9188605b5f88a804dd5207897fa70def80659c642fc18fa8f720d4ae0b5ba649 -/
section P2MFinalSource058

/-!
Exact original parent statement, composed from the good-height contour
estimate and the genuine endpoint transfer. All constituent source and
kernel evidence must be checked before this wrapper is treated as proved.
-/

set_option autoImplicit false

open Filter Asymptotics Real

namespace RiemannVonMangoldt

theorem dirichlet_L_zero_count :
    ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ T : ℝ, 2 ≤ T →
        |dirichletZeroCount χ T - T / π * Real.log (q * T / (2 * π * Real.exp 1))| ≤
          C * Real.log (q * T) := by
  exact CountBridge.dirichlet_L_zero_count_of_paired_good_heights
    CountBridge.dirichletZeroCount_good_height_error_uniform

end RiemannVonMangoldt

end P2MFinalSource058

section P2MFinalSolution
open Filter Asymptotics Real RiemannVonMangoldt

theorem solution :
    ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ T : ℝ, 2 ≤ T →
        |dirichletZeroCount χ T - T / π * Real.log (q * T / (2 * π * Real.exp 1))| ≤
          C * Real.log (q * T) := by
  exact RiemannVonMangoldt.dirichlet_L_zero_count

end P2MFinalSolution

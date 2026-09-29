-- Prove2me | solution 1 for Rudin.ch06_fundamental_theorem
-- status  : ACCEPTED   (disprove)
-- author  : @Lucas
-- created : 2026-09-18T18:28:24.498818+00:00
-- url     : https://prove2.me/submissions/6f1db7e3-fe4f-4d72-a1b7-4906ee17e051

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology Set

/-!
# Rudin, Theorem 6.21 without the boundedness hypothesis is false

Rudin's Chapter 6 assumes throughout (Definitions 6.1-6.2) that the integrand is bounded.  In
the formalization the upper and lower integrals are ordinary suprema and infima of sets of real
numbers, which take the default value `0` on unbounded sets, so the unbounded form of the
fundamental theorem of calculus admits a counterexample.

The counterexample is an increasing, everywhere differentiable `F` on `[0,1]` with `F 0 = 0`,
`F 1 = 1/3`, whose derivative `f = F'` is nonnegative, unbounded above on `[0,1]`, and has
infimum `0` on every nondegenerate subinterval.  Then every upper sum is nonnegative and the
one-interval partition gives the value `0`, so the upper integral is `0`; every lower sum is
`0`, so the lower integral is `0` as well.  Hence `f` is integrable with integral `0`, while
`F 1 - F 0 = 1/3`.

`F` is built in two layers, a Pompeiu-type function and a gluing of rescaled copies of it; see
the construction below.
-/

namespace Pom

/-! ## The dense sequence and the coefficients -/

/-- An enumeration of a dense subset of `[0,1]`, hitting `0` and `1`. -/
noncomputable def qq (n : ℕ) : ℝ := min 1 ((Nat.unpair n).1 / ((Nat.unpair n).2 + 1))

lemma qq_nonneg (n : ℕ) : 0 ≤ qq n := by
  have h : (0:ℝ) ≤ ((Nat.unpair n).1 : ℝ) / (((Nat.unpair n).2 : ℝ) + 1) := by positivity
  simpa [qq, le_min_iff] using h

lemma qq_le_one (n : ℕ) : qq n ≤ 1 := min_le_left _ _

lemma qq_mem (n : ℕ) : qq n ∈ Set.Icc (0:ℝ) 1 := ⟨qq_nonneg n, qq_le_one n⟩

lemma qq_zero : qq (Nat.pair 0 0) = 0 := by
  simp [qq, Nat.unpair_pair]

lemma qq_one : qq (Nat.pair 1 0) = 1 := by
  simp [qq, Nat.unpair_pair]

lemma qq_dense {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1) :
    ∃ n, u < qq n ∧ qq n < v := by
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn huv
  have hrpos : (0:ℝ) < (r : ℝ) := lt_of_le_of_lt hu hr1
  have hrlt : (r : ℝ) < 1 := lt_of_lt_of_le hr2 hv
  have hnum : 0 < r.num := by
    have : (0:ℚ) < r := by exact_mod_cast hrpos
    exact Rat.num_pos.mpr this
  refine ⟨Nat.pair r.num.toNat (r.den - 1), ?_, ?_⟩ <;>
  · have hden : ((r.den - 1 : ℕ) : ℝ) + 1 = (r.den : ℝ) := by
      have : (1:ℕ) ≤ r.den := r.pos
      have := Nat.sub_add_cancel this
      exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) this
    have hq : qq (Nat.pair r.num.toNat (r.den - 1)) = (r : ℝ) := by
      have hcast : ((r.num.toNat : ℕ) : ℝ) = (r.num : ℝ) := by
        have : (r.num.toNat : ℤ) = r.num := Int.toNat_of_nonneg hnum.le
        exact_mod_cast congrArg (fun k : ℤ => (k : ℝ)) this
      have : ((Nat.unpair (Nat.pair r.num.toNat (r.den - 1))).1 : ℝ)
          / (((Nat.unpair (Nat.pair r.num.toNat (r.den - 1))).2 : ℝ) + 1) = (r : ℝ) := by
        rw [Nat.unpair_pair]
        simp only []
        rw [hcast, hden, Rat.cast_def]
      rw [qq, this, min_eq_right hrlt.le]
    rw [hq]
    first
      | exact hr1
      | exact hr2

/-- The coefficients of the series. -/
noncomputable def cc (n : ℕ) : ℝ := (1/2:ℝ) ^ n

lemma cc_pos (n : ℕ) : 0 < cc n := by unfold cc; positivity

lemma summable_cc : Summable cc := by
  unfold cc
  exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

/-! ## The generator -/

/-- The generator `t ↦ sgn(t)·√|t|`. -/
noncomputable def gen (t : ℝ) : ℝ := Real.sqrt t - Real.sqrt (-t)

/-- Its derivative away from the origin. -/
noncomputable def dgen (t : ℝ) : ℝ := 1 / (2 * Real.sqrt |t|)

lemma gen_abs (t : ℝ) : |gen t| = Real.sqrt |t| := by
  rcases le_or_gt 0 t with h | h
  · rw [gen, Real.sqrt_eq_zero_of_nonpos (x := -t) (by linarith), sub_zero,
      abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg h]
  · rw [gen, Real.sqrt_eq_zero_of_nonpos (x := t) h.le, zero_sub, abs_neg,
      abs_of_nonneg (Real.sqrt_nonneg _), abs_of_neg h]

lemma gen_le_sqrt_abs (t : ℝ) : gen t ≤ Real.sqrt |t| := by
  have := abs_le.mp (le_of_eq (gen_abs t))
  linarith [(abs_le.mp (le_of_eq (gen_abs t))).2]

lemma neg_sqrt_abs_le_gen (t : ℝ) : -Real.sqrt |t| ≤ gen t := by
  have := abs_le.mp (le_of_eq (gen_abs t))
  linarith [(abs_le.mp (le_of_eq (gen_abs t))).1]

lemma gen_strictMono : StrictMono gen := by
  intro a b hab
  have h1 : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt hab.le
  have h2 : Real.sqrt (-b) ≤ Real.sqrt (-a) := Real.sqrt_le_sqrt (by linarith)
  rcases le_or_gt 0 a with ha | ha
  · have hb : Real.sqrt (-b) = 0 := Real.sqrt_eq_zero_of_nonpos (x := -b) (by linarith)
    have ha' : Real.sqrt (-a) = 0 := Real.sqrt_eq_zero_of_nonpos (x := -a) (by linarith)
    have : Real.sqrt a < Real.sqrt b := Real.sqrt_lt_sqrt ha hab
    unfold gen; rw [hb, ha']; linarith
  · rcases le_or_gt b 0 with hb | hb
    · have hsa : Real.sqrt a = 0 := Real.sqrt_eq_zero_of_nonpos (x := a) ha.le
      have hsb : Real.sqrt b = 0 := Real.sqrt_eq_zero_of_nonpos (x := b) hb
      have : Real.sqrt (-b) < Real.sqrt (-a) :=
        Real.sqrt_lt_sqrt (by linarith) (by linarith)
      unfold gen; rw [hsa, hsb]; linarith
    · have hsa : Real.sqrt a = 0 := Real.sqrt_eq_zero_of_nonpos (x := a) ha.le
      have hsb : Real.sqrt (-b) = 0 := Real.sqrt_eq_zero_of_nonpos (x := -b) (by linarith)
      have hpa : 0 < Real.sqrt (-a) := Real.sqrt_pos.mpr (by linarith)
      have hpb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
      unfold gen; rw [hsa, hsb]; linarith

lemma gen_mono : Monotone gen := gen_strictMono.monotone

lemma gen_zero : gen 0 = 0 := by simp [gen]

lemma hasDerivAt_neg_sqrt_neg {t : ℝ} (ht : t < 0) :
    HasDerivAt (fun x : ℝ => Real.sqrt (-x)) (-(1 / (2 * Real.sqrt (-t)))) t := by
  have hneg : HasDerivAt (fun x : ℝ => -x) (-1 : ℝ) t := hasDerivAt_neg t
  have h := (Real.hasDerivAt_sqrt (x := -t) (by linarith)).comp t hneg
  have hval : 1 / (2 * Real.sqrt (-t)) * (-1) = -(1 / (2 * Real.sqrt (-t))) := by ring
  rw [hval] at h
  simpa [Function.comp_def] using h

lemma hasDerivAt_gen {t : ℝ} (ht : t ≠ 0) : HasDerivAt gen (dgen t) t := by
  rcases lt_or_gt_of_ne ht with h | h
  · -- t < 0 : gen = -√(-t) near t
    have h1 := hasDerivAt_neg_sqrt_neg h
    have h2 : HasDerivAt (fun x : ℝ => Real.sqrt x) 0 t := by
      have hev : (fun x : ℝ => Real.sqrt x) =ᶠ[𝓝 t] (fun _ : ℝ => (0:ℝ)) := by
        filter_upwards [eventually_lt_nhds h] with x hx
        exact Real.sqrt_eq_zero_of_nonpos (x := x) hx.le
      exact (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq hev
    have key : HasDerivAt (fun x : ℝ => Real.sqrt x - Real.sqrt (-x))
        (0 - -(1 / (2 * Real.sqrt (-t)))) t := h2.sub h1
    have hval : dgen t = 0 - -(1 / (2 * Real.sqrt (-t))) := by
      rw [dgen, abs_of_neg h]; ring
    rw [hval]
    exact key
  · have h1 : HasDerivAt (fun x : ℝ => Real.sqrt x) (1 / (2 * Real.sqrt t)) t :=
      Real.hasDerivAt_sqrt (by linarith)
    have h2 : HasDerivAt (fun x : ℝ => Real.sqrt (-x)) 0 t := by
      have hev : (fun x : ℝ => Real.sqrt (-x)) =ᶠ[𝓝 t] (fun _ : ℝ => (0:ℝ)) := by
        filter_upwards [eventually_gt_nhds h] with x hx
        exact Real.sqrt_eq_zero_of_nonpos (x := -x) (by linarith)
      exact (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq hev
    have key : HasDerivAt (fun x : ℝ => Real.sqrt x - Real.sqrt (-x))
        (1 / (2 * Real.sqrt t) - 0) t := h1.sub h2
    have hval : dgen t = 1 / (2 * Real.sqrt t) - 0 := by
      rw [dgen, abs_of_pos h]; ring
    rw [hval]
    exact key

lemma dgen_nonneg (t : ℝ) : 0 ≤ dgen t := by
  unfold dgen; positivity

lemma dgen_pos {t : ℝ} (ht : t ≠ 0) : 0 < dgen t := by
  have : 0 < Real.sqrt |t| := Real.sqrt_pos.mpr (abs_pos.mpr ht)
  unfold dgen; positivity

end Pom

namespace Pom

lemma gen_of_nonneg {t : ℝ} (ht : 0 ≤ t) : gen t = Real.sqrt t := by
  rw [gen, Real.sqrt_eq_zero_of_nonpos (x := -t) (by linarith), sub_zero]

lemma gen_of_nonpos {t : ℝ} (ht : t ≤ 0) : gen t = -Real.sqrt (-t) := by
  rw [gen, Real.sqrt_eq_zero_of_nonpos (x := t) ht, zero_sub]

lemma gen_continuous : Continuous gen := by
  unfold gen
  exact Real.continuous_sqrt.sub (Real.continuous_sqrt.comp continuous_neg)

lemma gen_slope_nonneg (t : ℝ) {h : ℝ} (hh : h ≠ 0) : 0 ≤ (gen (t + h) - gen t) / h := by
  rcases lt_or_gt_of_ne hh with hneg | hpos
  · have hle : gen (t + h) ≤ gen t := gen_mono (by linarith)
    rw [div_nonneg_iff]
    exact Or.inr ⟨by linarith, hneg.le⟩
  · have hle : gen t ≤ gen (t + h) := gen_mono (by linarith)
    exact div_nonneg (by linarith) hpos.le

lemma sqrt_four_mul (x : ℝ) : Real.sqrt (4 * x) = 2 * Real.sqrt x := by
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
    show Real.sqrt 4 = 2 by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]]

/-- The difference quotients of `gen` at a point `t ≠ 0` are dominated by a fixed multiple of
the derivative at `t`, uniformly in the increment. -/
lemma gen_slope_le {t h : ℝ} (ht : t ≠ 0) (hh : h ≠ 0) :
    (gen (t + h) - gen t) / h ≤ 20 * dgen t := by
  have habs_t : 0 < |t| := abs_pos.mpr ht
  have habs_h : 0 < |h| := abs_pos.mpr hh
  have hu : 0 < Real.sqrt |t| := Real.sqrt_pos.mpr habs_t
  rcases le_or_gt (2 * |h|) |t| with hfar | hnear
  · -- far case : the mean value theorem on an interval avoiding the origin
    have hseg : ∀ x ∈ Set.Icc (min t (t + h)) (max t (t + h)), |t| / 2 ≤ |x| := by
      intro x hx
      have h1 : |x - t| ≤ |h| := by
        rcases le_or_gt 0 h with hpos | hneg
        · rw [min_eq_left (by linarith), max_eq_right (by linarith)] at hx
          rw [abs_of_nonneg (by linarith [hx.1])]
          linarith [hx.2, abs_of_nonneg hpos]
        · rw [min_eq_right (by linarith), max_eq_left (by linarith)] at hx
          rw [abs_of_nonpos (by linarith [hx.2])]
          linarith [hx.1, abs_of_neg hneg]
      have h3 : |t| - |x| ≤ |h| := by
        calc |t| - |x| ≤ |t - x| := abs_sub_abs_le_abs_sub t x
        _ = |x - t| := abs_sub_comm t x
        _ ≤ |h| := h1
      linarith
    have hlt : min t (t + h) < max t (t + h) := by
      rcases lt_or_gt_of_ne hh with hneg | hpos
      · rw [min_eq_right (by linarith), max_eq_left (by linarith)]; linarith
      · rw [min_eq_left (by linarith), max_eq_right (by linarith)]; linarith
    obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope gen dgen hlt
      gen_continuous.continuousOn
      (fun x hx => hasDerivAt_gen (by
        have hx' := hseg x ⟨le_of_lt hx.1, le_of_lt hx.2⟩
        intro h0
        rw [h0] at hx'
        simp at hx'
        linarith))
    have hcabs : |t| / 2 ≤ |c| := hseg c ⟨le_of_lt hc.1, le_of_lt hc.2⟩
    have hcpos : 0 < Real.sqrt |c| := Real.sqrt_pos.mpr (by linarith)
    have hslope : (gen (t + h) - gen t) / h
        = (gen (max t (t + h)) - gen (min t (t + h))) / (max t (t + h) - min t (t + h)) := by
      rcases lt_or_gt_of_ne hh with hneg | hpos
      · rw [min_eq_right (by linarith), max_eq_left (by linarith),
          show t - (t + h) = -h by ring, div_eq_div_iff (by linarith) (by linarith)]
        ring
      · rw [min_eq_left (by linarith), max_eq_right (by linarith),
          show t + h - t = h by ring]
    have hkey : Real.sqrt |t| ≤ 2 * Real.sqrt |c| := by
      have h1 : Real.sqrt |t| ≤ Real.sqrt (4 * |c|) := Real.sqrt_le_sqrt (by linarith)
      rwa [sqrt_four_mul |c|] at h1
    have hdgc : dgen c ≤ 2 * dgen t := by
      rw [dgen, dgen, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    rw [hslope, ← hceq]
    linarith [dgen_nonneg t]
  · -- near case : crude bounds on the increment of `gen`
    set s := Real.sqrt |h| with hs_def
    have hs : 0 < s := Real.sqrt_pos.mpr habs_h
    have hs2 : s ^ 2 = |h| := Real.sq_sqrt habs_h.le
    have hu2s : Real.sqrt |t| ≤ 2 * s := by
      have h1 : Real.sqrt |t| ≤ Real.sqrt (4 * |h|) := Real.sqrt_le_sqrt (by linarith)
      rwa [sqrt_four_mul |h|] at h1
    have hsq3 : Real.sqrt (3 * |h|) ≤ 2 * s := by
      have h1 : Real.sqrt (3 * |h|) ≤ Real.sqrt (4 * |h|) := Real.sqrt_le_sqrt (by linarith)
      rwa [sqrt_four_mul |h|] at h1
    have hgen3 : gen (3 * |h|) = Real.sqrt (3 * |h|) := gen_of_nonneg (by positivity)
    have hgen3' : gen (-(3 * |h|)) = -Real.sqrt (3 * |h|) := by
      rw [gen_of_nonpos (by linarith [abs_nonneg h] : -(3 * |h|) ≤ 0), neg_neg]
    have hup : ∀ y : ℝ, |y| ≤ 3 * |h| → |gen y| ≤ 2 * s := by
      intro y hy
      have hy1 : y ≤ 3 * |h| := le_trans (le_abs_self y) hy
      have hy2 : -(3 * |h|) ≤ y := by linarith [neg_abs_le y]
      have hA : gen y ≤ 2 * s := by
        have := gen_mono hy1
        rw [hgen3] at this; linarith
      have hB : -(2 * s) ≤ gen y := by
        have := gen_mono hy2
        rw [hgen3'] at this; linarith
      exact abs_le.mpr ⟨hB, hA⟩
    have hN : |gen (t + h) - gen t| ≤ 4 * s := by
      have h1 : |gen (t + h)| ≤ 2 * s := by
        refine hup _ ?_
        have := le_abs_self t
        have := neg_abs_le t
        have := le_abs_self h
        have := neg_abs_le h
        rw [abs_le]
        constructor <;> linarith
      have h2 : |gen t| ≤ 2 * s := by
        refine hup _ ?_
        rw [abs_le]
        constructor <;> linarith [le_abs_self t, neg_abs_le t]
      calc |gen (t + h) - gen t| ≤ |gen (t + h)| + |gen t| := abs_sub _ _
      _ ≤ 4 * s := by linarith
    have hpos : 0 ≤ (gen (t + h) - gen t) / h := gen_slope_nonneg t hh
    have heq : (gen (t + h) - gen t) / h = |gen (t + h) - gen t| / |h| := by
      rw [← abs_div, abs_of_nonneg hpos]
    rw [heq, show (20:ℝ) * dgen t = 20 / (2 * Real.sqrt |t|) by rw [dgen]; ring,
      div_le_div_iff₀ habs_h (by positivity)]
    nlinarith [hN, hu2s, hs, hs2, abs_nonneg (gen (t + h) - gen t), hu]

end Pom

namespace Pom

/-! ## The increasing function `gg` -/

lemma abs_term_le (x : ℝ) (n : ℕ) :
    |cc n * gen (x - qq n)| ≤ cc n * Real.sqrt (|x| + 1) := by
  have h1 : |gen (x - qq n)| = Real.sqrt |x - qq n| := gen_abs _
  have h2 : |x - qq n| ≤ |x| + 1 := by
    have := abs_sub (x) (qq n)
    have h3 : |qq n| ≤ 1 := by
      rw [abs_of_nonneg (qq_nonneg n)]
      exact qq_le_one n
    calc |x - qq n| ≤ |x| + |qq n| := abs_sub x (qq n)
    _ ≤ |x| + 1 := by linarith
  rw [abs_mul, abs_of_pos (cc_pos n), h1]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2) (cc_pos n).le

lemma summable_term (x : ℝ) : Summable (fun n => cc n * gen (x - qq n)) := by
  refine Summable.of_norm_bounded (g := fun n => cc n * Real.sqrt (|x| + 1))
    (summable_cc.mul_right _) ?_
  intro n
  simpa using abs_term_le x n

/-- The strictly increasing function whose inverse is the singular integrator. -/
noncomputable def gg (x : ℝ) : ℝ := ∑' n, cc n * gen (x - qq n)

lemma gg_strictMono : StrictMono gg := by
  intro a b hab
  refine (summable_term a).tsum_lt_tsum (i := 0) (fun n => ?_) ?_ (summable_term b)
  · exact mul_le_mul_of_nonneg_left (gen_mono (by linarith)) (cc_pos n).le
  · exact mul_lt_mul_of_pos_left (gen_strictMono (by linarith)) (cc_pos 0)

lemma gg_mono : Monotone gg := gg_strictMono.monotone

/-- A truncated version of the series, used to prove continuity locally. -/
noncomputable def ggTrunc (R : ℝ) (x : ℝ) : ℝ :=
  ∑' n, cc n * gen (max (-R) (min R (x - qq n)))

lemma ggTrunc_continuous {R : ℝ} (hR : 0 ≤ R) : Continuous (ggTrunc R) := by
  refine continuous_tsum (u := fun n => cc n * Real.sqrt R) (fun n => ?_)
    (summable_cc.mul_right _) (fun n x => ?_)
  · exact continuous_const.mul
      (gen_continuous.comp ((continuous_const.max (continuous_const.min
        (continuous_id.sub continuous_const)))))
  · have hb : |max (-R) (min R (x - qq n))| ≤ R := by
      rw [abs_le]
      constructor
      · exact le_max_left _ _
      · exact max_le (by linarith) (min_le_left _ _)
    have h1 : |gen (max (-R) (min R (x - qq n)))| = Real.sqrt |max (-R) (min R (x - qq n))| :=
      gen_abs _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (cc_pos n), h1]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb) (cc_pos n).le

lemma gg_eq_ggTrunc {R x : ℝ} (hx : |x| + 1 ≤ R) : gg x = ggTrunc R x := by
  refine tsum_congr (fun n => ?_)
  congr 1
  have h1 : |x - qq n| ≤ R := by
    have h3 : |qq n| ≤ 1 := by
      rw [abs_of_nonneg (qq_nonneg n)]; exact qq_le_one n
    calc |x - qq n| ≤ |x| + |qq n| := abs_sub x (qq n)
    _ ≤ R := by linarith
  have h2 := abs_le.mp h1
  rw [min_eq_right h2.2, max_eq_right h2.1]

lemma gg_continuous : Continuous gg := by
  rw [continuous_iff_continuousAt]
  intro x
  set R := |x| + 2 with hR_def
  have hR : 0 ≤ R := by positivity
  have hev : gg =ᶠ[𝓝 x] ggTrunc R := by
    have hball : ∀ᶠ y in 𝓝 x, |y - x| < 1 := by
      have : ∀ᶠ y in 𝓝 x, y ∈ Metric.ball x 1 := Metric.ball_mem_nhds x one_pos
      filter_upwards [this] with y hy
      rwa [Metric.mem_ball, Real.dist_eq] at hy
    filter_upwards [hball] with y hy
    refine gg_eq_ggTrunc ?_
    have : |y| ≤ |x| + 1 := by
      calc |y| = |x + (y - x)| := by ring_nf
      _ ≤ |x| + |y - x| := abs_add_le _ _
      _ ≤ |x| + 1 := by linarith
    linarith
  exact (ggTrunc_continuous hR).continuousAt.congr hev.symm

lemma gg_ge_of_ge_one {x : ℝ} (hx : 1 ≤ x) : Real.sqrt (x - 1) ≤ gg x := by
  have hterm : ∀ n, 0 ≤ cc n * gen (x - qq n) := by
    intro n
    refine mul_nonneg (cc_pos n).le ?_
    rw [← gen_zero]
    exact gen_mono (by linarith [qq_le_one n])
  have h0 : cc 0 * gen (x - qq 0) ≤ gg x :=
    (summable_term x).le_tsum 0 (fun j _ => hterm j)
  have h1 : cc 0 = 1 := by simp [cc]
  have h2 : Real.sqrt (x - 1) ≤ gen (x - qq 0) := by
    have : gen (x - 1) ≤ gen (x - qq 0) := gen_mono (by linarith [qq_le_one 0])
    rwa [gen_of_nonneg (by linarith)] at this
  rw [h1, one_mul] at h0
  linarith

lemma gg_le_of_le_zero {x : ℝ} (hx : x ≤ 0) : gg x ≤ -Real.sqrt (-x) := by
  have hterm : ∀ n, cc n * gen (x - qq n) ≤ 0 := by
    intro n
    refine mul_nonpos_of_nonneg_of_nonpos (cc_pos n).le ?_
    rw [← gen_zero]
    exact gen_mono (by linarith [qq_nonneg n])
  have h0 : gg x ≤ cc 0 * gen (x - qq 0) := by
    have hneg : Summable (fun n => -(cc n * gen (x - qq n))) := (summable_term x).neg
    have := hneg.le_tsum 0 (fun j _ => by simpa using hterm j)
    rw [tsum_neg] at this
    unfold gg
    linarith
  have h1 : cc 0 = 1 := by simp [cc]
  have h2 : gen (x - qq 0) ≤ -Real.sqrt (-x) := by
    have h3 : gen (x - qq 0) ≤ gen x := gen_mono (by linarith [qq_nonneg 0])
    rwa [gen_of_nonpos hx] at h3
  rw [h1, one_mul] at h0
  linarith

lemma gg_tendsto_atTop : Tendsto gg atTop atTop := by
  refine tendsto_atTop_mono' _ ?_ (Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ (-1)
    tendsto_id))
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  have h := gg_ge_of_ge_one hx
  simp only [Function.comp_apply, id_eq]
  rw [show x + -1 = x - 1 by ring]
  exact h

lemma gg_tendsto_atBot : Tendsto gg atBot atBot := by
  have hcomp : Tendsto (fun x : ℝ => -Real.sqrt (-x)) atBot atBot := by
    have h1 : Tendsto (fun x : ℝ => -x) atBot atTop := tendsto_neg_atBot_atTop
    have h2 : Tendsto (fun x : ℝ => Real.sqrt (-x)) atBot atTop := Real.tendsto_sqrt_atTop.comp h1
    exact tendsto_neg_atTop_atBot.comp h2
  refine tendsto_atBot_mono' _ ?_ hcomp
  filter_upwards [eventually_le_atBot (0:ℝ)] with x hx
  exact gg_le_of_le_zero hx

lemma gg_surjective : Function.Surjective gg :=
  gg_continuous.surjective gg_tendsto_atTop gg_tendsto_atBot

end Pom

namespace Pom

/-! ## The difference quotients of `gg` -/

/-- The candidate value of the derivative of `gg` at `x` (meaningful when the series
converges). -/
noncomputable def SS (x : ℝ) : ℝ := ∑' n, cc n * dgen (x - qq n)

lemma summable_slope {x y : ℝ} (hxy : y ≠ x) :
    Summable (fun n => cc n * ((gen (y - qq n) - gen (x - qq n)) / (y - x))) := by
  have h := ((summable_term y).sub (summable_term x)).mul_right (y - x)⁻¹
  refine h.congr (fun n => ?_)
  field_simp

lemma slope_gg {x y : ℝ} (hxy : y ≠ x) :
    slope gg x y = ∑' n, cc n * ((gen (y - qq n) - gen (x - qq n)) / (y - x)) := by
  rw [slope_def_field, gg, gg, ← (summable_term y).tsum_sub (summable_term x),
    div_eq_mul_inv, ← tsum_mul_right]
  exact tsum_congr (fun n => by field_simp)

lemma gen_div_self {u : ℝ} (hu : u ≠ 0) : gen u / u = 2 * dgen u := by
  rcases lt_or_gt_of_ne hu with hneg | hpos
  · have h1 : Real.sqrt (-u) * Real.sqrt (-u) = -u := Real.mul_self_sqrt (by linarith)
    have hsn : 0 < Real.sqrt (-u) := Real.sqrt_pos.mpr (by linarith)
    rw [gen_of_nonpos hneg.le, dgen, abs_of_neg hneg, div_eq_iff hu]
    field_simp
    nlinarith [h1, hsn]
  · have h1 : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt (by linarith)
    have hsn : 0 < Real.sqrt u := Real.sqrt_pos.mpr hpos
    rw [gen_of_nonneg hpos.le, dgen, abs_of_pos hpos, div_eq_iff hu]
    field_simp
    nlinarith [h1, hsn]

lemma slope_term_nonneg (x : ℝ) {y : ℝ} (hxy : y ≠ x) (n : ℕ) :
    0 ≤ cc n * ((gen (y - qq n) - gen (x - qq n)) / (y - x)) := by
  have hne : y - x ≠ 0 := sub_ne_zero.mpr hxy
  have h := gen_slope_nonneg (x - qq n) hne
  have heq : x - qq n + (y - x) = y - qq n := by ring
  rw [heq] at h
  exact mul_nonneg (cc_pos n).le h

lemma slope_term_le {x : ℝ} (hne : ∀ n, x ≠ qq n) {y : ℝ} (hxy : y ≠ x) (n : ℕ) :
    cc n * ((gen (y - qq n) - gen (x - qq n)) / (y - x)) ≤ 20 * (cc n * dgen (x - qq n)) := by
  have hne' : y - x ≠ 0 := sub_ne_zero.mpr hxy
  have ht : x - qq n ≠ 0 := sub_ne_zero.mpr (hne n)
  have h := gen_slope_le ht hne'
  have heq : x - qq n + (y - x) = y - qq n := by ring
  rw [heq] at h
  calc cc n * ((gen (y - qq n) - gen (x - qq n)) / (y - x))
      ≤ cc n * (20 * dgen (x - qq n)) := by
        exact mul_le_mul_of_nonneg_left h (cc_pos n).le
  _ = 20 * (cc n * dgen (x - qq n)) := by ring

/-- Each individual term's difference quotient converges to the term's derivative. -/
lemma tendsto_slope_term {x : ℝ} (hne : ∀ n, x ≠ qq n) (k : ℕ) :
    Tendsto (fun y => cc k * ((gen (y - qq k) - gen (x - qq k)) / (y - x))) (𝓝[≠] x)
      (𝓝 (cc k * dgen (x - qq k))) := by
  have h1 : HasDerivAt (fun y : ℝ => y - qq k) 1 x := (hasDerivAt_id x).sub_const _
  have hd : HasDerivAt (fun y : ℝ => gen (y - qq k)) (dgen (x - qq k)) x := by
    have h2 := (hasDerivAt_gen (sub_ne_zero.mpr (hne k))).comp x h1
    simpa [Function.comp_def] using h2
  have h3 := (hasDerivAt_iff_tendsto_slope.mp hd).const_mul (cc k)
  refine h3.congr (fun y => ?_)
  rw [slope_def_field]

/-- If the series of derivatives converges at `x` (and `x` is not one of the singular points),
the difference quotients of `gg` converge to its sum. -/
lemma tendsto_slope_gg_of_good {x : ℝ} (hne : ∀ n, x ≠ qq n)
    (hsum : Summable (fun n => cc n * dgen (x - qq n))) :
    Tendsto (slope gg x) (𝓝[≠] x) (𝓝 (SS x)) := by
  have key : Tendsto (fun y => ∑' n, cc n * ((gen (y - qq n) - gen (x - qq n)) / (y - x)))
      (𝓝[≠] x) (𝓝 (∑' n, cc n * dgen (x - qq n))) := by
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun n => 20 * (cc n * dgen (x - qq n))) (hsum.mul_left 20)
      (fun k => tendsto_slope_term hne k) ?_
    filter_upwards [self_mem_nhdsWithin] with y hy k
    have hxy : y ≠ x := hy
    rw [Real.norm_eq_abs, abs_of_nonneg (slope_term_nonneg x hxy k)]
    exact slope_term_le hne hxy k
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (slope_gg (x := x) (y := y) hy).symm

/-- The derivative of `gg` is positive : the sum dominates its zeroth term. -/
lemma SS_pos {x : ℝ} (hne : ∀ n, x ≠ qq n)
    (hsum : Summable (fun n => cc n * dgen (x - qq n))) : 0 < SS x := by
  have h0 : cc 0 * dgen (x - qq 0) ≤ SS x :=
    hsum.le_tsum 0 (fun j _ => mul_nonneg (cc_pos j).le (dgen_nonneg _))
  have hpos : 0 < cc 0 * dgen (x - qq 0) :=
    mul_pos (cc_pos 0) (dgen_pos (sub_ne_zero.mpr (hne 0)))
  linarith

/-! ## The divergent cases -/

lemma tendsto_dgen_atTop (x : ℝ) :
    Tendsto (fun y : ℝ => dgen (y - x)) (𝓝[≠] x) atTop := by
  rw [tendsto_atTop]
  intro K
  have hcont : Tendsto (fun y : ℝ => |y - x|) (𝓝[≠] x) (𝓝 0) := by
    have : Tendsto (fun y : ℝ => |y - x|) (𝓝 x) (𝓝 |x - x|) :=
      (continuous_abs.comp (continuous_id.sub continuous_const)).tendsto x
    simpa using this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ y in 𝓝[≠] x, |y - x| < 1 / (4 * K ^ 2 + 1) := by
    have hpos : (0:ℝ) < 1 / (4 * K ^ 2 + 1) := by positivity
    exact hcont (Iio_mem_nhds hpos)
  filter_upwards [hev, self_mem_nhdsWithin] with y hy hy2
  have hne : y - x ≠ 0 := sub_ne_zero.mpr hy2
  have habs : 0 < |y - x| := abs_pos.mpr hne
  have hs : 0 < Real.sqrt |y - x| := Real.sqrt_pos.mpr habs
  have hsq : Real.sqrt |y - x| ^ 2 = |y - x| := Real.sq_sqrt habs.le
  have hbound : (4 * K ^ 2 + 1) * |y - x| < 1 := by
    rw [← lt_div_iff₀' (by positivity)]
    simpa using hy
  have : K ≤ 1 / (2 * Real.sqrt |y - x|) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hs, hsq, sq_nonneg (2 * K * Real.sqrt |y - x| - 1)]
  simpa [dgen] using this

lemma tendsto_slope_gg_atTop_of_mem {x : ℝ} {m : ℕ} (hm : x = qq m) :
    Tendsto (slope gg x) (𝓝[≠] x) atTop := by
  have hterm : ∀ y : ℝ, y ≠ x →
      cc m * (2 * dgen (y - x)) ≤ slope gg x y := by
    intro y hxy
    have hsum := summable_slope (x := x) (y := y) hxy
    have hle := hsum.le_tsum m (fun j _ => slope_term_nonneg x hxy j)
    have heq : cc m * ((gen (y - qq m) - gen (x - qq m)) / (y - x)) = cc m * (2 * dgen (y - x)) := by
      rw [← hm, sub_self, gen_zero, sub_zero]
      congr 1
      exact gen_div_self (sub_ne_zero.mpr hxy)
    rw [heq] at hle
    rw [slope_gg hxy]
    exact hle
  have htend : Tendsto (fun y : ℝ => cc m * (2 * dgen (y - x))) (𝓝[≠] x) atTop := by
    have h1 := (tendsto_dgen_atTop x).const_mul_atTop (show (0:ℝ) < 2 by norm_num)
    exact h1.const_mul_atTop (cc_pos m)
  refine tendsto_atTop_mono' _ ?_ htend
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact hterm y hy

lemma tendsto_slope_gg_atTop_of_not_summable {x : ℝ} (hne : ∀ n, x ≠ qq n)
    (hns : ¬ Summable (fun n => cc n * dgen (x - qq n))) :
    Tendsto (slope gg x) (𝓝[≠] x) atTop := by
  rw [tendsto_atTop]
  intro K
  have hnn : ∀ n, 0 ≤ cc n * dgen (x - qq n) := fun n =>
    mul_nonneg (cc_pos n).le (dgen_nonneg _)
  have hdiv : Tendsto (fun N => ∑ i ∈ Finset.range N, cc i * dgen (x - qq i)) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).mp hns
  obtain ⟨N, hN⟩ := (tendsto_atTop.mp hdiv (K + 1)) |>.exists
  have hfin : Tendsto
      (fun y => ∑ i ∈ Finset.range N, cc i * ((gen (y - qq i) - gen (x - qq i)) / (y - x)))
      (𝓝[≠] x) (𝓝 (∑ i ∈ Finset.range N, cc i * dgen (x - qq i))) :=
    tendsto_finsetSum _ (fun i _ => tendsto_slope_term hne i)
  have hev : ∀ᶠ y in 𝓝[≠] x,
      K < ∑ i ∈ Finset.range N, cc i * ((gen (y - qq i) - gen (x - qq i)) / (y - x)) := by
    have hK : K < ∑ i ∈ Finset.range N, cc i * dgen (x - qq i) := by linarith
    exact hfin (Ioi_mem_nhds hK)
  filter_upwards [hev, self_mem_nhdsWithin] with y hy hy2
  have hxy : y ≠ x := hy2
  have hsum := summable_slope (x := x) (y := y) hxy
  have hle := hsum.sum_le_tsum (Finset.range N) (fun j _ => slope_term_nonneg x hxy j)
  rw [slope_gg hxy]
  linarith

end Pom

namespace Pom

/-! ## The inverse function -/

/-- `gg` as an order isomorphism of the line. -/
noncomputable def ggIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective gg gg_strictMono gg_surjective

/-- The Pompeiu-type function : the inverse of `gg`. -/
noncomputable def Ph (y : ℝ) : ℝ := ggIso.symm y

lemma ggIso_apply (x : ℝ) : ggIso x = gg x := rfl

lemma Ph_gg (x : ℝ) : Ph (gg x) = x := by
  simp [Ph, ← ggIso_apply]

lemma gg_Ph (y : ℝ) : gg (Ph y) = y := ggIso.apply_symm_apply y

lemma Ph_strictMono : StrictMono Ph := fun _ _ hab => ggIso.symm.strictMono hab

lemma Ph_injective : Function.Injective Ph := Ph_strictMono.injective

lemma Ph_continuous : Continuous Ph := (OrderIso.toHomeomorph ggIso.symm).continuous

lemma tendsto_Ph_punctured (x : ℝ) : Tendsto Ph (𝓝[≠] (gg x)) (𝓝[≠] x) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h := Ph_continuous.tendsto (gg x)
    rw [Ph_gg] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : y ≠ gg x := hy
    intro hcon
    apply hy'
    have : Ph y = Ph (gg x) := by rw [hcon, Ph_gg]
    have := Ph_injective this
    exact this

lemma Ph_slope_eq {x y : ℝ} (hy : y ≠ gg x) : slope Ph (gg x) y = (slope gg x (Ph y))⁻¹ := by
  have hne : Ph y ≠ x := by
    intro hcon
    apply hy
    have : gg (Ph y) = gg x := by rw [hcon]
    rwa [gg_Ph] at this
  rw [slope_def_field, slope_def_field, Ph_gg, gg_Ph, inv_div]

/-- At every point the inverse function is differentiable. -/
lemma Ph_hasDerivAt_good {x : ℝ} (hne : ∀ n, x ≠ qq n)
    (hsum : Summable (fun n => cc n * dgen (x - qq n))) :
    HasDerivAt Ph (SS x)⁻¹ (gg x) := by
  rw [hasDerivAt_iff_tendsto_slope]
  have h1 : Tendsto (fun y => slope gg x (Ph y)) (𝓝[≠] (gg x)) (𝓝 (SS x)) :=
    (tendsto_slope_gg_of_good hne hsum).comp (tendsto_Ph_punctured x)
  have h2 := h1.inv₀ (SS_pos hne hsum).ne'
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (Ph_slope_eq hy).symm

lemma Ph_hasDerivAt_of_atTop {x : ℝ} (h : Tendsto (slope gg x) (𝓝[≠] x) atTop) :
    HasDerivAt Ph 0 (gg x) := by
  rw [hasDerivAt_iff_tendsto_slope]
  have h1 : Tendsto (fun y => slope gg x (Ph y)) (𝓝[≠] (gg x)) atTop :=
    h.comp (tendsto_Ph_punctured x)
  have h2 : Tendsto (fun y => (slope gg x (Ph y))⁻¹) (𝓝[≠] (gg x)) (𝓝 0) :=
    h1.inv_tendsto_atTop
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (Ph_slope_eq hy).symm

lemma Ph_hasDerivAt (y : ℝ) : ∃ L : ℝ, 0 ≤ L ∧ HasDerivAt Ph L y := by
  set x := Ph y with hx
  have hy : y = gg x := (gg_Ph y).symm
  by_cases hmem : ∃ m, x = qq m
  · obtain ⟨m, hm⟩ := hmem
    refine ⟨0, le_rfl, ?_⟩
    rw [hy]
    exact Ph_hasDerivAt_of_atTop (tendsto_slope_gg_atTop_of_mem hm)
  · push_neg at hmem
    by_cases hsum : Summable (fun n => cc n * dgen (x - qq n))
    · refine ⟨(SS x)⁻¹, le_of_lt (inv_pos.mpr (SS_pos hmem hsum)), ?_⟩
      rw [hy]
      exact Ph_hasDerivAt_good hmem hsum
    · refine ⟨0, le_rfl, ?_⟩
      rw [hy]
      exact Ph_hasDerivAt_of_atTop (tendsto_slope_gg_atTop_of_not_summable hmem hsum)

lemma Ph_differentiableAt (y : ℝ) : DifferentiableAt ℝ Ph y := by
  obtain ⟨L, _, hL⟩ := Ph_hasDerivAt y
  exact hL.differentiableAt

lemma Ph_deriv_nonneg (y : ℝ) : 0 ≤ deriv Ph y := by
  obtain ⟨L, hL0, hL⟩ := Ph_hasDerivAt y
  rwa [hL.deriv]

lemma Ph_deriv_qq (n : ℕ) : deriv Ph (gg (qq n)) = 0 :=
  (Ph_hasDerivAt_of_atTop (tendsto_slope_gg_atTop_of_mem (x := qq n) (m := n) rfl)).deriv

lemma Ph_hasDerivAt_deriv (y : ℝ) : HasDerivAt Ph (deriv Ph y) y :=
  (Ph_differentiableAt y).hasDerivAt

end Pom

namespace Pom

/-! ## The normalized building block `Psi` -/

noncomputable def AA : ℝ := gg 0

noncomputable def BB : ℝ := gg 1 - gg 0

lemma BB_pos : 0 < BB := by
  have := gg_strictMono (show (0:ℝ) < 1 by norm_num)
  simp [BB]; linarith

/-- The Pompeiu function rescaled so that it maps `[0,1]` onto `[0,1]`. -/
noncomputable def Psi0 (t : ℝ) : ℝ := Ph (AA + t * BB)

lemma Psi0_zero : Psi0 0 = 0 := by
  simp [Psi0, AA, Ph_gg]

lemma Psi0_one : Psi0 1 = 1 := by
  have : AA + 1 * BB = gg 1 := by simp [AA, BB]
  rw [Psi0, this, Ph_gg]

lemma Psi0_strictMono : StrictMono Psi0 := by
  intro a b hab
  exact Ph_strictMono (by nlinarith [BB_pos])

lemma Psi0_continuous : Continuous Psi0 :=
  Ph_continuous.comp (by fun_prop)

lemma Psi0_hasDerivAt (t : ℝ) :
    HasDerivAt Psi0 (BB * deriv Ph (AA + t * BB)) t := by
  have h1 : HasDerivAt (fun s : ℝ => AA + s * BB) BB t := by
    simpa using ((hasDerivAt_id t).mul_const BB).const_add AA
  have h2 := (Ph_hasDerivAt_deriv (AA + t * BB)).comp t h1
  have h3 : HasDerivAt Psi0 (deriv Ph (AA + t * BB) * BB) t := h2
  rw [mul_comm]
  exact h3

/-- The clamped version, constant outside `[0,1]`. -/
noncomputable def Psi (t : ℝ) : ℝ := max 0 (min 1 (Psi0 t))

lemma Psi_nonneg (t : ℝ) : 0 ≤ Psi t := le_max_left _ _

lemma Psi_le_one (t : ℝ) : Psi t ≤ 1 := max_le (by norm_num) (min_le_left _ _)

lemma Psi_mono : Monotone Psi := by
  intro a b hab
  exact max_le_max le_rfl (min_le_min le_rfl (Psi0_strictMono.monotone hab))

lemma Psi_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : Psi t = 0 := by
  have h : Psi0 t ≤ 0 := by
    rcases eq_or_lt_of_le ht with h | h
    · simp [h, Psi0_zero]
    · exact le_of_lt (by simpa [Psi0_zero] using Psi0_strictMono h)
  have : min 1 (Psi0 t) ≤ 0 := le_trans (min_le_right _ _) h
  simp [Psi, max_eq_left this]

lemma Psi_eq_one_of_one_le {t : ℝ} (ht : 1 ≤ t) : Psi t = 1 := by
  have h : 1 ≤ Psi0 t := by
    rcases eq_or_lt_of_le ht with h | h
    · simp [← h, Psi0_one]
    · exact le_of_lt (by simpa [Psi0_one] using Psi0_strictMono h)
  simp [Psi, min_eq_left h]

lemma Psi_zero : Psi 0 = 0 := Psi_eq_zero_of_nonpos le_rfl

lemma Psi_one : Psi 1 = 1 := Psi_eq_one_of_one_le le_rfl

lemma clamp_diff_le {u v : ℝ} (h : u ≤ v) :
    max 0 (min 1 v) - max 0 (min 1 u) ≤ v - u := by
  simp only [max_def, min_def]
  split_ifs <;> linarith

lemma clamp_mono {u v : ℝ} (h : u ≤ v) : max 0 (min 1 u) ≤ max 0 (min 1 v) :=
  max_le_max le_rfl (min_le_min le_rfl h)

lemma Psi_lipschitz (a b : ℝ) : |Psi a - Psi b| ≤ |Psi0 a - Psi0 b| := by
  rcases le_total (Psi0 a) (Psi0 b) with h | h
  · have h1 := clamp_diff_le h
    have h2 := clamp_mono h
    rw [abs_of_nonpos (by simpa [Psi] using sub_nonpos.mpr h2),
      abs_of_nonpos (by linarith)]
    simpa [Psi] using h1
  · have h1 := clamp_diff_le h
    have h2 := clamp_mono h
    rw [abs_of_nonneg (by simpa [Psi] using sub_nonneg.mpr h2),
      abs_of_nonneg (by linarith)]
    simpa [Psi] using h1

/-- The derivative of the building block. -/
noncomputable def dPsi (t : ℝ) : ℝ :=
  if 0 < t ∧ t < 1 then BB * deriv Ph (AA + t * BB) else 0

lemma dPsi_nonneg (t : ℝ) : 0 ≤ dPsi t := by
  unfold dPsi
  split
  · exact mul_nonneg BB_pos.le (Ph_deriv_nonneg _)
  · exact le_rfl

lemma dPsi_eq_zero_of_not_mem {t : ℝ} (ht : ¬ (0 < t ∧ t < 1)) : dPsi t = 0 := by
  simp [dPsi, ht]

/-- If the clamped function has vanishing derivative bound at a boundary point, use the
Lipschitz estimate. -/
lemma Psi_hasDerivAt_of_Psi0_deriv_zero {t : ℝ} (h : HasDerivAt Psi0 0 t) :
    HasDerivAt Psi 0 t := by
  rw [hasDerivAt_iff_tendsto_slope]
  have h0 := hasDerivAt_iff_tendsto_slope.mp h
  refine squeeze_zero_norm ?_ (by simpa using h0.norm)
  intro y
  simp only [Real.norm_eq_abs, slope_def_field, abs_div]
  rcases eq_or_ne y t with rfl | hyt
  · simp
  · have hpos : 0 < |y - t| := abs_pos.mpr (sub_ne_zero.mpr hyt)
    rw [div_le_div_iff₀ hpos hpos]
    nlinarith [Psi_lipschitz y t, hpos]

lemma Psi_hasDerivAt (t : ℝ) : HasDerivAt Psi (dPsi t) t := by
  by_cases ht : 0 < t ∧ t < 1
  · -- interior : `Psi` agrees with `Psi0` near `t`
    have h1 : 0 < Psi0 t := by simpa [Psi0_zero] using Psi0_strictMono ht.1
    have h2 : Psi0 t < 1 := by simpa [Psi0_one] using Psi0_strictMono ht.2
    have hev : Psi =ᶠ[𝓝 t] Psi0 := by
      have hopen : ∀ᶠ y in 𝓝 t, 0 < Psi0 y ∧ Psi0 y < 1 := by
        have ha : ∀ᶠ y in 𝓝 t, 0 < Psi0 y :=
          (Psi0_continuous.tendsto t) (Ioi_mem_nhds h1)
        have hb : ∀ᶠ y in 𝓝 t, Psi0 y < 1 :=
          (Psi0_continuous.tendsto t) (Iio_mem_nhds h2)
        exact ha.and hb
      filter_upwards [hopen] with y hy
      rw [Psi, min_eq_right hy.2.le, max_eq_right hy.1.le]
    have := (Psi0_hasDerivAt t).congr_of_eventuallyEq hev
    rw [dPsi, if_pos ht]
    exact this
  · rw [dPsi, if_neg ht]
    rcases lt_trichotomy t 0 with hlt | heq | hgt
    · -- to the left of `0` the function vanishes identically
      have hev : Psi =ᶠ[𝓝 t] fun _ => 0 := by
        filter_upwards [eventually_lt_nhds hlt] with y hy
        exact Psi_eq_zero_of_nonpos hy.le
      exact (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq hev
    · -- at `0` : the derivative of `Psi0` vanishes there
      subst heq
      refine Psi_hasDerivAt_of_Psi0_deriv_zero ?_
      have h := Psi0_hasDerivAt 0
      have hz : AA + 0 * BB = gg (qq (Nat.pair 0 0)) := by rw [qq_zero]; simp [AA]
      rw [hz, Ph_deriv_qq] at h
      simpa using h
    · -- to the right of `1`, or at `1`
      have h1t : 1 ≤ t := by
        by_contra hcon
        exact ht ⟨hgt, lt_of_not_ge hcon⟩
      rcases eq_or_lt_of_le h1t with heq1 | hgt1
      · -- `t = 1`
        refine Psi_hasDerivAt_of_Psi0_deriv_zero ?_
        have h := Psi0_hasDerivAt t
        have hz : AA + t * BB = gg (qq (Nat.pair 1 0)) := by
          rw [qq_one, ← heq1]; simp [AA, BB]
        rw [hz, Ph_deriv_qq] at h
        simpa using h
      · have hev : Psi =ᶠ[𝓝 t] fun _ => 1 := by
          filter_upwards [eventually_gt_nhds hgt1] with y hy
          exact Psi_eq_one_of_one_le hy.le
        exact (hasDerivAt_const t (1:ℝ)).congr_of_eventuallyEq hev

lemma deriv_Psi (t : ℝ) : deriv Psi t = dPsi t := (Psi_hasDerivAt t).deriv

/-- Somewhere in `(0,1)` the derivative of the building block equals `1`. -/
lemma exists_dPsi_eq_one : ∃ t ∈ Set.Ioo (0:ℝ) 1, dPsi t = 1 := by
  obtain ⟨t, ht, hteq⟩ := exists_hasDerivAt_eq_slope Psi dPsi (by norm_num : (0:ℝ) < 1)
    (Continuous.continuousOn (by
      have : Continuous Psi := by
        refine continuous_iff_continuousAt.mpr (fun t => (Psi_hasDerivAt t).continuousAt)
      exact this))
    (fun x _ => Psi_hasDerivAt x)
  refine ⟨t, ht, ?_⟩
  rw [hteq, Psi_one, Psi_zero]
  norm_num

/-- The zeros of the derivative are dense. -/
lemma exists_dPsi_eq_zero {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1) :
    ∃ t, u < t ∧ t < v ∧ dPsi t = 0 := by
  have hPu : 0 ≤ Psi0 u := by
    rcases eq_or_lt_of_le hu with h | h
    · rw [← h, Psi0_zero]
    · exact le_of_lt (by simpa [Psi0_zero] using Psi0_strictMono h)
  have hPv : Psi0 v ≤ 1 := by
    rcases eq_or_lt_of_le hv with h | h
    · rw [h, Psi0_one]
    · exact le_of_lt (by simpa [Psi0_one] using Psi0_strictMono h)
  obtain ⟨n, hn1, hn2⟩ := qq_dense hPu (Psi0_strictMono huv) hPv
  refine ⟨(gg (qq n) - AA) / BB, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ BB_pos]
    have : Psi0 u < qq n := hn1
    have h2 : gg (Psi0 u) < gg (qq n) := gg_strictMono this
    rw [Psi0, gg_Ph] at h2
    linarith
  · rw [div_lt_iff₀ BB_pos]
    have h2 : gg (qq n) < gg (Psi0 v) := gg_strictMono hn2
    rw [Psi0, gg_Ph] at h2
    linarith
  · have harg : AA + ((gg (qq n) - AA) / BB) * BB = gg (qq n) := by
      rw [div_mul_eq_mul_div, mul_div_assoc, div_self BB_pos.ne', mul_one]
      ring
    rw [dPsi]
    split
    · rw [harg, Ph_deriv_qq, mul_zero]
    · rfl

end Pom

namespace Pom

/-! ## The singular integrator -/

/-- Left endpoints of the copies. -/
noncomputable def pp (m : ℕ) : ℝ := (1/2:ℝ) ^ (m + 1)

/-- Widths of the copies. -/
noncomputable def vv (m : ℕ) : ℝ := (1/8:ℝ) ^ (m + 1)

/-- Heights of the copies. -/
noncomputable def ww (m : ℕ) : ℝ := (1/4:ℝ) ^ (m + 1)

lemma pp_pos (m : ℕ) : 0 < pp m := by unfold pp; positivity
lemma vv_pos (m : ℕ) : 0 < vv m := by unfold vv; positivity
lemma ww_pos (m : ℕ) : 0 < ww m := by unfold ww; positivity

lemma vv_lt_pp (m : ℕ) : vv m < pp m :=
  pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)

lemma pp_le_half (m : ℕ) : pp m ≤ 1/2 := by
  have : (1/2:ℝ) ^ (m + 1) ≤ (1/2:ℝ) ^ 1 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  simpa [pp] using this

lemma vv_le_eighth (m : ℕ) : vv m ≤ 1/8 := by
  have : (1/8:ℝ) ^ (m + 1) ≤ (1/8:ℝ) ^ 1 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  simpa [vv] using this

lemma pp_antitone {m k : ℕ} (h : m ≤ k) : pp k ≤ pp m :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

lemma vv_antitone {m k : ℕ} (h : m ≤ k) : vv k ≤ vv m :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

lemma ww_eq_pp_sq (m : ℕ) : ww m = pp m ^ 2 := by
  unfold ww pp
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

lemma ww_div_vv (m : ℕ) : ww m / vv m = 2 ^ (m + 1) := by
  unfold ww vv
  rw [div_eq_iff (by positivity), ← mul_pow]
  norm_num

lemma copy_lt_next {m k : ℕ} (h : m < k) : pp k + vv k < pp m := by
  have h1 : pp k ≤ pp (m + 1) := pp_antitone (by omega)
  have h2 : vv k ≤ vv (m + 1) := vv_antitone (by omega)
  have h3 : pp (m + 1) + vv (m + 1) < pp m := by
    have e1 : pp (m + 1) = (1/2) * pp m := by unfold pp; ring
    have e2 : vv (m + 1) = (1/8) * vv m := by unfold vv; ring
    have e3 : vv m < pp m := vv_lt_pp m
    have e4 : 0 < vv m := vv_pos m
    rw [e1, e2]; linarith
  linarith

lemma copy_sum_antitone {m k : ℕ} (h : m ≤ k) : pp k + vv k ≤ pp m + vv m := by
  have := pp_antitone h
  have := vv_antitone h
  linarith

/-- The `m`-th copy of the building block. -/
noncomputable def term (m : ℕ) (x : ℝ) : ℝ := ww m * Psi ((x - pp m) / vv m)

lemma term_nonneg (m : ℕ) (x : ℝ) : 0 ≤ term m x :=
  mul_nonneg (ww_pos m).le (Psi_nonneg _)

lemma term_le (m : ℕ) (x : ℝ) : term m x ≤ ww m := by
  have h1 : Psi ((x - pp m) / vv m) ≤ 1 := Psi_le_one _
  calc term m x ≤ ww m * 1 := mul_le_mul_of_nonneg_left h1 (ww_pos m).le
  _ = ww m := mul_one _

lemma term_eq_zero {m : ℕ} {x : ℝ} (hx : x ≤ pp m) : term m x = 0 := by
  have : (x - pp m) / vv m ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (vv_pos m).le
  rw [term, Psi_eq_zero_of_nonpos this, mul_zero]

lemma term_eq_ww {m : ℕ} {x : ℝ} (hx : pp m + vv m ≤ x) : term m x = ww m := by
  have : 1 ≤ (x - pp m) / vv m := by
    rw [le_div_iff₀ (vv_pos m)]
    linarith
  rw [term, Psi_eq_one_of_one_le this, mul_one]

lemma term_mono (m : ℕ) : Monotone (term m) := by
  intro a b hab
  refine mul_le_mul_of_nonneg_left ?_ (ww_pos m).le
  refine Psi_mono ?_
  have := vv_pos m
  gcongr

lemma term_hasDerivAt (m : ℕ) (x : ℝ) :
    HasDerivAt (term m) (ww m / vv m * dPsi ((x - pp m) / vv m)) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y - pp m) / vv m) (1 / vv m) x := by
    simpa using ((hasDerivAt_id x).sub_const (pp m)).div_const (vv m)
  have h2 := (Psi_hasDerivAt ((x - pp m) / vv m)).comp x h1
  have h3 : HasDerivAt (fun y : ℝ => Psi ((y - pp m) / vv m))
      (dPsi ((x - pp m) / vv m) * (1 / vv m)) x := h2
  have h4 := h3.const_mul (ww m)
  have h5 : ww m * (dPsi ((x - pp m) / vv m) * (1 / vv m))
      = ww m / vv m * dPsi ((x - pp m) / vv m) := by ring
  rw [← h5]
  exact h4

lemma summable_ww : Summable ww := by
  have h : Summable (fun m : ℕ => (1/4:ℝ) ^ m) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine (h.mul_right (1/4 : ℝ)).congr (fun m => ?_)
  unfold ww
  ring

lemma summable_copy (x : ℝ) : Summable (fun m => term m x) :=
  Summable.of_nonneg_of_le (fun m => term_nonneg m x) (fun m => term_le m x) summable_ww

/-- The singular integrator. -/
noncomputable def alpha (x : ℝ) : ℝ := ∑' m, term m x

lemma alpha_mono : Monotone alpha := by
  intro a b hab
  exact (summable_copy a).tsum_le_tsum (fun m => term_mono m hab) (summable_copy b)

lemma alpha_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : alpha x = 0 := by
  have h : ∀ m, term m x = 0 := fun m => term_eq_zero (le_trans hx (pp_pos m).le)
  simp [alpha, h]

lemma alpha_zero : alpha 0 = 0 := alpha_eq_zero_of_nonpos le_rfl

lemma tsum_ww : ∑' m, ww m = 1/3 := by
  have h : ∑' m : ℕ, (1/4:ℝ) ^ m = (1 - 1/4)⁻¹ :=
    tsum_geometric_of_lt_one (r := (1/4:ℝ)) (by norm_num) (by norm_num)
  calc ∑' m, ww m = ∑' m : ℕ, (1/4:ℝ) ^ m * (1/4) := by
        refine tsum_congr (fun m => ?_); unfold ww; ring
  _ = (∑' m : ℕ, (1/4:ℝ) ^ m) * (1/4) := tsum_mul_right
  _ = 1/3 := by rw [h]; norm_num

lemma alpha_one : alpha 1 = 1/3 := by
  have hterm : ∀ m, term m 1 = ww m := by
    intro m
    refine term_eq_ww ?_
    have := pp_le_half m
    have := vv_le_eighth m
    linarith
  rw [alpha, tsum_congr hterm, tsum_ww]

lemma alpha_lt : alpha 0 < alpha 1 := by
  rw [alpha_zero, alpha_one]; norm_num

/-! ### Local structure -/

lemma alpha_eq_finite {M : ℕ} {y : ℝ} (hy : pp M + vv M < y) :
    alpha y = (∑ m ∈ Finset.range M, term m y) + ∑' k, ww (k + M) := by
  have h1 := (summable_copy y).sum_add_tsum_nat_add M
  rw [alpha, ← h1]
  congr 1
  refine tsum_congr (fun k => ?_)
  refine term_eq_ww ?_
  have := copy_sum_antitone (m := M) (k := k + M) (by omega)
  linarith

lemma alpha_hasDerivAt_of_gt {M : ℕ} {x : ℝ} (hx : pp M + vv M < x) :
    HasDerivAt alpha (∑ m ∈ Finset.range M, ww m / vv m * dPsi ((x - pp m) / vv m)) x := by
  have hev : alpha =ᶠ[𝓝 x] fun y => (∑ m ∈ Finset.range M, term m y) + ∑' k, ww (k + M) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact alpha_eq_finite hy
  have hsum : HasDerivAt (fun y => ∑ m ∈ Finset.range M, term m y)
      (∑ m ∈ Finset.range M, ww m / vv m * dPsi ((x - pp m) / vv m)) x :=
    HasDerivAt.fun_sum (fun m _ => term_hasDerivAt m x)
  have hd := hsum.add_const (∑' k, ww (k + M))
  exact hd.congr_of_eventuallyEq hev

/-! ### The derivative at the origin -/

lemma exists_pp_lt {y : ℝ} (hy : 0 < y) : ∃ m, pp m < y := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hy (by norm_num : (1/2:ℝ) < 1)
  refine ⟨n, lt_of_le_of_lt ?_ hn⟩
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

lemma alpha_le_sq {y : ℝ} (hy : 0 < y) : alpha y ≤ 2 * y ^ 2 := by
  classical
  have hex := exists_pp_lt hy
  set m₀ := Nat.find hex with hm₀
  have h1 : pp m₀ < y := Nat.find_spec hex
  have h2 : ∀ m, m < m₀ → y ≤ pp m := fun m hm => not_lt.mp (Nat.find_min hex hm)
  have hfirst : (∑ m ∈ Finset.range m₀, term m y) = 0 :=
    Finset.sum_eq_zero (fun m hm => term_eq_zero (h2 m (Finset.mem_range.mp hm)))
  have hsplit := (summable_copy y).sum_add_tsum_nat_add m₀
  have htail : ∑' k, term (k + m₀) y ≤ ∑' k, ww (k + m₀) := by
    refine Summable.tsum_le_tsum (fun k => term_le (k + m₀) y) ?_ ?_
    · exact (summable_copy y).comp_injective (add_left_injective m₀)
    · exact summable_ww.comp_injective (add_left_injective m₀)
  have hgeo : ∑' k, ww (k + m₀) = (4/3) * ww m₀ := by
    have hrw : ∀ k : ℕ, ww (k + m₀) = ww m₀ * (1/4:ℝ) ^ k := by
      intro k
      unfold ww
      rw [show k + m₀ + 1 = (m₀ + 1) + k by omega, pow_add]
    calc ∑' k, ww (k + m₀) = ∑' k : ℕ, ww m₀ * (1/4:ℝ) ^ k := tsum_congr hrw
    _ = ww m₀ * ∑' k : ℕ, (1/4:ℝ) ^ k := tsum_mul_left
    _ = (4/3) * ww m₀ := by
        rw [tsum_geometric_of_lt_one (r := (1/4:ℝ)) (by norm_num) (by norm_num)]; ring
  have hchain : alpha y = ∑' k, term (k + m₀) y := by
    rw [alpha, ← hsplit, hfirst, zero_add]
  have hpp2 : pp m₀ ^ 2 < y ^ 2 := by
    have := pp_pos m₀
    nlinarith
  rw [hchain]
  calc ∑' k, term (k + m₀) y ≤ ∑' k, ww (k + m₀) := htail
  _ = (4/3) * ww m₀ := hgeo
  _ = (4/3) * pp m₀ ^ 2 := by rw [ww_eq_pp_sq]
  _ ≤ 2 * y ^ 2 := by nlinarith

lemma alpha_hasDerivAt_zero : HasDerivAt alpha 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  refine squeeze_zero_norm (a := fun y : ℝ => 2 * |y|) ?_ ?_
  · intro y
    rw [slope_def_field, alpha_zero, sub_zero, sub_zero, Real.norm_eq_abs, abs_div]
    rcases lt_trichotomy y 0 with hneg | rfl | hpos
    · rw [alpha_eq_zero_of_nonpos hneg.le]
      simp
    · simp
    · have h1 : alpha y ≤ 2 * y ^ 2 := alpha_le_sq hpos
      have h2 : 0 ≤ alpha y := by
        rw [← alpha_zero]
        exact alpha_mono hpos.le
      rw [abs_of_nonneg h2, abs_of_pos hpos, div_le_iff₀ hpos]
      nlinarith
  · have h : Tendsto (fun y : ℝ => 2 * |y|) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun y : ℝ => 2 * |y|) := by fun_prop
      have := hc.tendsto (0:ℝ)
      simpa using this
    exact h.mono_left nhdsWithin_le_nhds

end Pom

namespace Pom

lemma exists_copy_lt {x : ℝ} (hx : 0 < x) : ∃ M, pp M + vv M < x := by
  obtain ⟨M, hM⟩ := exists_pp_lt (show (0:ℝ) < x / 2 by linarith)
  refine ⟨M, ?_⟩
  have := vv_lt_pp M
  linarith

lemma alpha_differentiable {x : ℝ} (hx : 0 ≤ x) : HasDerivAt alpha (deriv alpha x) x := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h]
    have h0 := alpha_hasDerivAt_zero
    rw [h0.deriv]
    exact h0
  · obtain ⟨M, hM⟩ := exists_copy_lt h
    have hd := alpha_hasDerivAt_of_gt hM
    rw [hd.deriv]
    exact hd

lemma deriv_alpha_zero : deriv alpha 0 = 0 := alpha_hasDerivAt_zero.deriv

/-- Away from the interiors of the copies the derivative vanishes. -/
lemma deriv_alpha_eq_zero {x : ℝ} (hx : 0 < x)
    (h : ∀ m, ¬ (pp m < x ∧ x < pp m + vv m)) : deriv alpha x = 0 := by
  obtain ⟨M, hM⟩ := exists_copy_lt hx
  have hd := alpha_hasDerivAt_of_gt hM
  rw [hd.deriv]
  refine Finset.sum_eq_zero (fun m _ => ?_)
  have hzero : dPsi ((x - pp m) / vv m) = 0 := by
    refine dPsi_eq_zero_of_not_mem ?_
    rintro ⟨h1, h2⟩
    refine h m ⟨?_, ?_⟩
    · have := (div_pos_iff).mp h1
      rcases this with ⟨ha, _⟩ | ⟨_, hb⟩
      · linarith
      · exact absurd hb (not_lt.mpr (vv_pos m).le)
    · rw [div_lt_one (vv_pos m)] at h2
      linarith
  rw [hzero, mul_zero]

/-- On the `m`-th copy the derivative is the rescaled derivative of the building block. -/
lemma deriv_alpha_copy (m : ℕ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    deriv alpha (pp m + vv m * t) = 2 ^ (m + 1) * dPsi t := by
  set x := pp m + vv m * t with hx_def
  have hvm : 0 < vv m := vv_pos m
  have hvne : vv m ≠ 0 := hvm.ne'
  have hxlt : x < pp m + vv m := by
    have : vv m * t < vv m * 1 := by exact mul_lt_mul_of_pos_left ht1 hvm
    simp only [hx_def]; linarith
  have hxgt : pp m < x := by
    have : 0 < vv m * t := mul_pos hvm ht0
    simp only [hx_def]; linarith
  have hM : pp (m + 1) + vv (m + 1) < x := lt_trans (copy_lt_next (by omega)) hxgt
  have hd := alpha_hasDerivAt_of_gt hM
  rw [hd.deriv]
  have hsplit : ∑ j ∈ Finset.range (m + 1), ww j / vv j * dPsi ((x - pp j) / vv j)
      = ww m / vv m * dPsi ((x - pp m) / vv m) := by
    rw [Finset.sum_range_succ]
    have hzero : ∑ j ∈ Finset.range m, ww j / vv j * dPsi ((x - pp j) / vv j) = 0 := by
      refine Finset.sum_eq_zero (fun j hj => ?_)
      have hjm : j < m := Finset.mem_range.mp hj
      have hpj : pp m + vv m < pp j := copy_lt_next hjm
      have harg : (x - pp j) / vv j < 0 := by
        refine div_neg_of_neg_of_pos (by linarith) (vv_pos j)
      have : dPsi ((x - pp j) / vv j) = 0 := by
        refine dPsi_eq_zero_of_not_mem ?_
        rintro ⟨h1, _⟩
        linarith
      rw [this, mul_zero]
    rw [hzero, zero_add]
  rw [hsplit]
  have hargm : (x - pp m) / vv m = t := by
    rw [hx_def, add_sub_cancel_left, mul_comm, mul_div_assoc, div_self hvne, mul_one]
  rw [hargm, ww_div_vv]

/-- The derivative is unbounded above on `[0,1]`. -/
lemma alpha_deriv_unbounded (K : ℝ) : ∃ x ∈ Set.Icc (0:ℝ) 1, K < deriv alpha x := by
  obtain ⟨t, ht, ht1⟩ := exists_dPsi_eq_one
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt K (by norm_num : (1:ℝ) < 2)
  refine ⟨pp m + vv m * t, ?_, ?_⟩
  · constructor
    · have := (pp_pos m).le
      have := mul_nonneg (vv_pos m).le ht.1.le
      linarith
    · have h1 := pp_le_half m
      have h2 : vv m * t ≤ vv m := by
        have := (vv_pos m).le
        nlinarith [ht.2, vv_pos m]
      have h3 := vv_le_eighth m
      linarith
  · rw [deriv_alpha_copy m ht.1 ht.2, ht1, mul_one]
    calc K < 2 ^ m := hm
    _ ≤ 2 ^ (m + 1) := by
        refine pow_le_pow_right₀ (by norm_num) (by omega)

/-- The derivative takes arbitrarily small values on every nondegenerate subinterval. -/
lemma alpha_deriv_small {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1) :
    ∃ x ∈ Set.Icc u v, deriv alpha x = 0 := by
  classical
  rcases eq_or_lt_of_le hu with hzero | hupos
  · refine ⟨0, ⟨le_of_eq hzero.symm, by linarith⟩, ?_⟩
    exact deriv_alpha_zero
  by_cases hin : ∃ j, pp j < u ∧ u < pp j + vv j
  · obtain ⟨j, hj1, hj2⟩ := hin
    by_cases hvj : v ≤ pp j + vv j
    · -- the whole interval lies inside the `j`-th copy
      have hvv : 0 < vv j := vv_pos j
      have hvne : vv j ≠ 0 := hvv.ne'
      set u' := (u - pp j) / vv j with hu'_def
      set v' := (v - pp j) / vv j with hv'_def
      have hu' : 0 ≤ u' := le_of_lt (div_pos (by linarith) hvv)
      have huv' : u' < v' := by
        have h1 : v' - u' = (v - u) / vv j := by
          rw [hu'_def, hv'_def, div_sub_div_same]
          ring_nf
        have h2 : 0 < (v - u) / vv j := div_pos (by linarith) hvv
        linarith
      have hv1 : v' ≤ 1 := by
        rw [hv'_def, div_le_one hvv]
        linarith
      obtain ⟨t, htu, htv, ht0⟩ := exists_dPsi_eq_zero hu' huv' hv1
      have hue : pp j + vv j * u' = u := by
        rw [hu'_def, mul_comm, div_mul_cancel₀ _ hvne]
        ring
      have hve : pp j + vv j * v' = v := by
        rw [hv'_def, mul_comm, div_mul_cancel₀ _ hvne]
        ring
      refine ⟨pp j + vv j * t, ⟨?_, ?_⟩, ?_⟩
      · have : vv j * u' < vv j * t := by exact mul_lt_mul_of_pos_left htu hvv
        linarith [hue]
      · have : vv j * t < vv j * v' := by exact mul_lt_mul_of_pos_left htv hvv
        linarith [hve]
      · rw [deriv_alpha_copy j (lt_of_le_of_lt hu' htu) (lt_of_lt_of_le htv hv1), ht0, mul_zero]
    · -- the right endpoint of the copy lies in the interval
      refine ⟨pp j + vv j, ⟨by linarith, by linarith [not_le.mp hvj]⟩, ?_⟩
      refine deriv_alpha_eq_zero (by linarith [pp_pos j, vv_pos j]) ?_
      intro m
      rintro ⟨h1, h2⟩
      rcases lt_trichotomy m j with hmj | hmj | hmj
      · have := copy_lt_next hmj
        linarith
      · subst hmj
        linarith
      · have := copy_lt_next hmj
        linarith
  · push_neg at hin
    refine ⟨u, ⟨le_rfl, huv.le⟩, ?_⟩
    refine deriv_alpha_eq_zero hupos ?_
    intro m
    rintro ⟨h1, h2⟩
    exact absurd h2 (not_lt.mpr (hin m h1))

end Pom

namespace Pom

/-- **Existence of a singular integrator.** -/
theorem exists_singular_integrator :
    ∃ α : ℝ → ℝ, Monotone α ∧
      (∀ x ∈ Set.Icc (0:ℝ) 1, HasDerivAt α (deriv α x) x) ∧
      α 0 < α 1 ∧
      (∀ K : ℝ, ∃ x ∈ Set.Icc (0:ℝ) 1, K < deriv α x) ∧
      (∀ u v : ℝ, 0 ≤ u → u < v → v ≤ 1 → ∀ ε > 0, ∃ x ∈ Set.Icc u v, deriv α x < ε) := by
  refine ⟨alpha, alpha_mono, fun x hx => alpha_differentiable hx.1, alpha_lt,
    alpha_deriv_unbounded, ?_⟩
  intro u v hu huv hv ε hε
  obtain ⟨x, hx, hx0⟩ := alpha_deriv_small hu huv hv
  exact ⟨x, hx, by rw [hx0]; exact hε⟩

end Pom

namespace RudinSingularAux

open Rudin

/-- Division points of a partition increase with the index. -/
lemma x_mono {a b : ℝ} (P : Partition a b) :
    ∀ {i j : ℕ}, i ≤ j → j ≤ P.n → P.x i ≤ P.x j := by
  intro i j hij hjn
  induction j with
  | zero =>
      have : i = 0 := Nat.le_zero.mp hij
      simp [this]
  | succ k ih =>
      have hk : k < P.n := hjn
      rcases Nat.eq_or_lt_of_le hij with h | h
      · exact le_of_eq (by rw [h])
      · have hik : i ≤ k := Nat.lt_succ_iff.mp h
        exact (ih hik (le_of_lt hk)).trans (P.mono k hk)

/-- Every division point lies in the interval. -/
lemma x_mem {a b : ℝ} (P : Partition a b) {i : ℕ} (hi : i ≤ P.n) : P.x i ∈ Set.Icc a b := by
  constructor
  · have h := x_mono P (Nat.zero_le i) hi
    rwa [P.first] at h
  · have h := x_mono P hi (le_refl P.n)
    rwa [P.last] at h

/-- The trivial partition of `[0, 1]` with a single subinterval. -/
def trivPart : Partition (0:ℝ) 1 where
  n := 1
  x := fun i => if i = 0 then 0 else 1
  first := by simp
  last := by norm_num
  mono := by
    intro i hi
    interval_cases i
    norm_num

lemma trivPart_x0 : trivPart.x 0 = 0 := rfl

lemma trivPart_x1 : trivPart.x 1 = 1 := rfl

section

variable {g : ℝ → ℝ}

/-- Every upper sum of a nonnegative integrand (with `α = id`) is nonnegative. -/
lemma upperSum_nonneg (hnn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ g x) (P : Partition (0:ℝ) 1) :
    0 ≤ upperSum g id P := by
  refine Finset.sum_nonneg ?_
  intro i hi
  have hi' : i < P.n := Finset.mem_range.mp hi
  have hle : P.x i ≤ P.x (i + 1) := P.mono i hi'
  have hmi : P.x i ∈ Set.Icc (0:ℝ) 1 := x_mem P (le_of_lt hi')
  have hsup : 0 ≤ sSup (g '' Set.Icc (P.x i) (P.x (i + 1))) := by
    by_cases hb : BddAbove (g '' Set.Icc (P.x i) (P.x (i + 1)))
    · exact le_trans (hnn _ hmi) (le_csSup hb ⟨P.x i, ⟨le_rfl, hle⟩, rfl⟩)
    · simp [Real.sSup_of_not_bddAbove hb]
  have hfac : (0:ℝ) ≤ id (P.x (i + 1)) - id (P.x i) := by
    simpa using sub_nonneg.mpr hle
  exact mul_nonneg hsup hfac

/-- If a nonnegative integrand is unbounded above on `[0, 1]`, its upper integral is `0`:
the one-interval partition already gives the value `0`, and no upper sum is negative. -/
lemma upperIntegral_eq_zero (hnn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ g x)
    (hunb : ¬ BddAbove (g '' Set.Icc (0:ℝ) 1)) : upperIntegral 0 1 g id = 0 := by
  have h0 : upperSum g id trivPart = 0 := by
    simp [upperSum, trivPart, Real.sSup_of_not_bddAbove hunb]
  have hmem : (0:ℝ) ∈ {y : ℝ | ∃ P : Partition (0:ℝ) 1, y = upperSum g id P} := ⟨trivPart, h0.symm⟩
  have hlb : ∀ y ∈ {y : ℝ | ∃ P : Partition (0:ℝ) 1, y = upperSum g id P}, (0:ℝ) ≤ y := by
    rintro y ⟨P, rfl⟩
    exact upperSum_nonneg hnn P
  refine le_antisymm (csInf_le ⟨0, fun y hy => hlb y hy⟩ hmem) (le_csInf ⟨0, hmem⟩ hlb)

/-- If a nonnegative function takes arbitrarily small values on every nondegenerate
subinterval, then its infimum over any such subinterval is `0`. -/
lemma sInf_eq_zero_of_small (hnn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ g x)
    (hsmall : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ 1 → ∀ ε > 0, ∃ x ∈ Set.Icc u v, g x < ε)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1) : sInf (g '' Set.Icc u v) = 0 := by
  have hsub : Set.Icc u v ⊆ Set.Icc (0:ℝ) 1 := Set.Icc_subset_Icc hu hv
  have hbdd : BddBelow (g '' Set.Icc u v) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hnn x (hsub hx)
  have hne : (g '' Set.Icc u v).Nonempty := ⟨g u, u, ⟨le_rfl, huv.le⟩, rfl⟩
  refine le_antisymm ?_ (le_csInf hne (by rintro _ ⟨x, hx, rfl⟩; exact hnn x (hsub hx)))
  by_contra hpos
  rw [not_le] at hpos
  obtain ⟨x, hx, hlt⟩ := hsmall u v hu huv hv _ hpos
  exact absurd (csInf_le hbdd ⟨x, hx, rfl⟩) (not_le.mpr hlt)

/-- Under the same hypotheses every lower sum vanishes. -/
lemma lowerSum_eq_zero (hnn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ g x)
    (hsmall : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ 1 → ∀ ε > 0, ∃ x ∈ Set.Icc u v, g x < ε)
    (P : Partition (0:ℝ) 1) : lowerSum g id P = 0 := by
  refine Finset.sum_eq_zero ?_
  intro i hi
  have hi' : i < P.n := Finset.mem_range.mp hi
  have hle : P.x i ≤ P.x (i + 1) := P.mono i hi'
  rcases eq_or_lt_of_le hle with h | h
  · simp [h]
  · have hmi : P.x i ∈ Set.Icc (0:ℝ) 1 := x_mem P (le_of_lt hi')
    have hmi1 : P.x (i + 1) ∈ Set.Icc (0:ℝ) 1 := x_mem P (Nat.succ_le_of_lt hi')
    have h0 := sInf_eq_zero_of_small hnn hsmall hmi.1 h hmi1.2
    simp [h0]

/-- Hence the lower integral vanishes too. -/
lemma lowerIntegral_eq_zero (hnn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ g x)
    (hsmall : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ 1 → ∀ ε > 0, ∃ x ∈ Set.Icc u v, g x < ε) :
    lowerIntegral 0 1 g id = 0 := by
  have hset : {y : ℝ | ∃ P : Partition (0:ℝ) 1, y = lowerSum g id P} = {0} := by
    ext y
    constructor
    · rintro ⟨P, rfl⟩
      simp [lowerSum_eq_zero hnn hsmall P]
    · rintro rfl
      exact ⟨trivPart, (lowerSum_eq_zero hnn hsmall trivPart).symm⟩
  unfold lowerIntegral
  rw [hset, csSup_singleton]

end

end RudinSingularAux


open Rudin RudinSingularAux

/-- Rudin's Theorem 6.21 fails without the boundedness hypothesis of Definition 6.1. -/
theorem solution :
    ¬ ∀ (a b : ℝ), a ≤ b → ∀ (f F : ℝ → ℝ), RiemannIntegrable a b f →
        (∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x) → RiemannIntegral a b f = F b - F a := by
  intro hthm
  obtain ⟨α, hmono, hdiff, hgrow, hunb, hsmall⟩ := Pom.exists_singular_integrator
  have hnn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ deriv α x := fun x _ => hmono.deriv_nonneg
  have hunb' : ¬ BddAbove (deriv α '' Set.Icc (0:ℝ) 1) := by
    rintro ⟨K, hK⟩
    obtain ⟨x, hx, hlt⟩ := hunb K
    exact absurd (hK ⟨x, hx, rfl⟩) (not_le.mpr hlt)
  have hup : upperIntegral 0 1 (deriv α) id = 0 := upperIntegral_eq_zero hnn hunb'
  have hlo : lowerIntegral 0 1 (deriv α) id = 0 := lowerIntegral_eq_zero hnn hsmall
  have hint : RiemannIntegrable 0 1 (deriv α) := by
    unfold RiemannIntegrable RSIntegrable
    rw [hup, hlo]
  have hval : RiemannIntegral 0 1 (deriv α) = 0 := by
    unfold RiemannIntegral RSIntegral
    exact hup
  have := hthm 0 1 (by norm_num) (deriv α) α hint hdiff
  rw [hval] at this
  linarith

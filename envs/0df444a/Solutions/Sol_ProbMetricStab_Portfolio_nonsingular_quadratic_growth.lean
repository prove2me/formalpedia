-- Prove2me | solution 1 for ProbMetricStab.Portfolio.nonsingular_quadratic_growth
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:17:31.82998+00:00
-- url     : https://prove2.me/submissions/7bd5817d-80c3-4db5-a6a2-d22d5edd3662

import Mathlib
import Definitions.Def_ProbMetricStab_Portfolio_Setting

open MeasureTheory Set
open scoped ENNReal
namespace ProbMetricStab.Portfolio

private lemma scalar_strong (α : ℝ) (hα : 1 < α) (hα2 : α < 2) :
    StrongConvexOn (Icc (-1 : ℝ) 1) (α * (α - 1)) (fun z : ℝ => |z| ^ α) := by
  let m := α * (α - 1)
  let f := fun z : ℝ => z ^ α - m / 2 * z ^ 2
  let d := fun z : ℝ => α * z ^ (α - 1) - m * z
  let dd := fun z : ℝ => α * (α - 1) * z ^ (α - 2) - m
  have hd (z : ℝ) : HasDerivAt f (d z) z := by
    have hh := (Real.hasDerivAt_rpow_const (x := z) (Or.inr hα.le)).sub
      (((hasDerivAt_id z).pow 2).const_mul (m / 2))
    convert! hh using 1 <;> dsimp [f, d] <;> ring
  have hdd (z : ℝ) (hz : 0 < z) : HasDerivAt d (dd z) z := by
    have hh := ((Real.hasDerivAt_rpow_const (x := z) (p := α - 1) (Or.inl hz.ne')).const_mul α).sub
      ((hasDerivAt_id z).const_mul m)
    convert! hh using 1
    dsimp [d, dd]
    rw [show α - 1 - 1 = α - 2 by ring]
    ring
  have hc : Continuous f := by
    exact (Real.continuous_rpow_const (by linarith : 0 ≤ α)).sub
      ((continuous_id.pow 2).const_mul (m / 2))
  have hconv : ConvexOn ℝ (Icc (0 : ℝ) 1) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (f' := d) (f'' := dd) (convex_Icc 0 1) hc.continuousOn
    · intro z hz; exact (hd z).hasDerivWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      exact (hdd z hz.1).hasDerivWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      have hh := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hz.1 hz.2.le
        (by linarith : α - 2 ≤ 0)
      dsimp [dd, m]
      nlinarith [mul_pos (by linarith : 0 < α) (by linarith : 0 < α - 1)]
  have hmono : MonotoneOn f (Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hc.continuousOn
    · exact fun z _ => (hd z).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      rw [(hd z).deriv]
      have hp : z ≤ z ^ (α - 1) := by
        simpa using Real.rpow_le_rpow_of_exponent_ge hz.1 hz.2.le (by linarith : α - 1 ≤ 1)
      dsimp [d, m]
      have hm : α * (α - 1) ≤ α := by nlinarith
      have hmul := mul_le_mul_of_nonneg_right hm hz.1.le
      nlinarith [mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ α)]
  apply strongConvexOn_iff_convex.mpr
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : |x| ∈ Icc (0 : ℝ) 1 := ⟨abs_nonneg _, abs_le.mpr hx⟩
  have hy' : |y| ∈ Icc (0 : ℝ) 1 := ⟨abs_nonneg _, abs_le.mpr hy⟩
  have hsum : a * |x| + b * |y| ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · nlinarith [mul_le_mul_of_nonneg_left hx'.2 ha, mul_le_mul_of_nonneg_left hy'.2 hb]
  have habs : |a * x + b * y| ≤ a * |x| + b * |y| := by
    calc
      _ ≤ |a * x| + |b * y| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have hh := (hmono ⟨abs_nonneg _, habs.trans hsum.2⟩ hsum habs).trans
    (hconv.2 hx' hy' ha hb hab)
  simpa only [f, m, smul_eq_mul, Real.norm_eq_abs, sq_abs] using hh


private lemma norm_simplex {s : ℕ} {x : Rs s} (hx : x ∈ simplex s) : ‖x‖ ≤ 1 := by
  have hi (i : Fin s) : x i ≤ 1 := by
    rw [← hx.2]
    exact Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
  have hs : ‖x‖ ^ 2 ≤ 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, ← hx.2]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [hx.1 i, hi i]
  nlinarith [norm_nonneg x]

private lemma power_lip (α : ℝ) (hα : 1 ≤ α) {a b : ℝ}
    (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) :
    |a ^ α - b ^ α| ≤ α * |a - b| := by
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := fun z : ℝ => z ^ α) (C := α)
    (fun z _ => (Real.differentiable_rpow_const hα) z)
    (fun z hz => ?_) (convex_Icc 0 1) hb ha
  · simpa only [Real.norm_eq_abs] using hh
  · rw [Real.deriv_rpow_const, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hz.1 _))]
    calc
      α * z ^ (α - 1) ≤ α * 1 :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_one hz.1 hz.2 (by linarith)) (by linarith)
      _ = α := mul_one α

private lemma inner_bound {s : ℕ} {x ξ : Rs s} (hx : x ∈ simplex s)
    (hξ : ξ ∈ unitSphere s) : |inner ℝ x ξ| ≤ 1 := by
  have hn : ‖ξ‖ = 1 := by simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using hξ
  calc
    _ ≤ ‖x‖ * ‖ξ‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 := by rw [hn, mul_one]; exact norm_simplex hx


private lemma convex_simplex (s : ℕ) : Convex ℝ (simplex s) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    change 0 ≤ a * x i + b * y i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · change (∑ i : Fin s, (a * x i + b * y i)) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx.2, hy.2]
    linarith

private lemma compact_simplex (s : ℕ) : IsCompact (simplex s) := by
  have hh := (isCompact_stdSimplex ℝ (Fin s)).image (PiLp.continuous_toLp 2 (fun _ : Fin s => ℝ))
  convert hh using 1
  ext x
  constructor
  · intro hx
    exact ⟨WithLp.ofLp x, hx, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

private lemma continuous_f0 {s : ℕ} (α : ℝ) (hα : 0 ≤ α) (x : Rs s) :
    Continuous (fun ξ => f0 α ξ x) := by
  exact ((continuous_const.inner continuous_id).abs).rpow_const (fun _ => Or.inr hα)

private lemma f0_integrable {s : ℕ} (Γ : Measure (Rs s)) (hΓ : IsSpectral Γ)
    (α : ℝ) (hα : 0 ≤ α) {x : Rs s} (hx : x ∈ simplex s) :
    IntegrableOn (fun ξ => f0 α ξ x) (unitSphere s) Γ := by
  letI := hΓ.1
  apply (integrable_const (1 : ℝ)).mono' (continuous_f0 α hα x).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (Metric.isClosed_sphere.measurableSet)] with ξ hξ
  unfold f0
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact Real.rpow_le_one (abs_nonneg _) (inner_bound hx hξ) hα

private lemma continuous_risk {s : ℕ} (Γ : Measure (Rs s)) (hΓ : IsSpectral Γ)
    (α : ℝ) (hα : 0 ≤ α) : ContinuousOn (risk α Γ) (simplex s) := by
  letI := hΓ.1
  apply continuousOn_of_dominated (bound := fun _ => (1 : ℝ))
  · intro x hx
    exact (continuous_f0 α hα x).aestronglyMeasurable
  · intro x hx
    filter_upwards [ae_restrict_mem (Metric.isClosed_sphere.measurableSet)] with ξ hξ
    unfold f0
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_one (abs_nonneg _) (inner_bound hx hξ) hα
  · exact integrable_const _
  · apply Filter.Eventually.of_forall
    intro ξ
    exact (((continuous_id.inner continuous_const).abs).rpow_const (fun _ => Or.inr hα)).continuousOn

private lemma quadratic_integrable {s : ℕ} (Γ : Measure (Rs s)) (hΓ : IsSpectral Γ) (x : Rs s) :
    IntegrableOn (fun ξ => |inner ℝ x ξ| ^ 2) (unitSphere s) Γ := by
  letI := hΓ.1
  refine (integrable_const (‖x‖ ^ 2)).mono'
    ((show Continuous (fun ξ : Rs s => |inner ℝ x ξ| ^ 2) from
      ((continuous_const.inner continuous_id).abs).pow 2)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (Metric.isClosed_sphere.measurableSet)] with ξ hξ
  have hn : ‖ξ‖ = 1 := by simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using hξ
  have hh := abs_real_inner_le_norm x ξ
  rw [hn, mul_one] at hh
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (abs_nonneg _) hh 2

private lemma risk_strong {s : ℕ} (Γ : Measure (Rs s)) (hΓ : IsSpectral Γ)
    (c : ℝ) (hc : 0 < c)
    (hbound : ∀ x : Rs s, c * ‖x‖ ^ 2 ≤ ∫ ξ in unitSphere s, |inner ℝ x ξ| ^ 2 ∂Γ)
    (α : ℝ) (hα : 1 < α) (hα2 : α < 2) :
    StrongConvexOn (simplex s) (c * α * (α - 1)) (risk α Γ) := by
  let m := α * (α - 1)
  refine ⟨convex_simplex s, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy : a • x + b • y ∈ simplex s := convex_simplex s hx hy ha hb hab
  have hi := f0_integrable Γ hΓ α (by linarith) hx
  have hj := f0_integrable Γ hΓ α (by linarith) hy
  have hk := f0_integrable Γ hΓ α (by linarith) hxy
  have hq := quadratic_integrable Γ hΓ (x - y)
  have hh :
      risk α Γ (a • x + b • y) ≤ a * risk α Γ x + b * risk α Γ y -
        a * b * (m / 2) * ∫ ξ in unitSphere s, |inner ℝ (x - y) ξ| ^ 2 ∂Γ := by
    calc
      _ ≤ ∫ ξ in unitSphere s,
          (a * f0 α ξ x + b * f0 α ξ y - a * b * (m / 2) * |inner ℝ (x - y) ξ| ^ 2) ∂Γ := by
        apply integral_mono_ae hk ((hi.const_mul a).add (hj.const_mul b) |>.sub (hq.const_mul (a * b * (m / 2))))
        filter_upwards [ae_restrict_mem (Metric.isClosed_sphere.measurableSet)] with ξ hξ
        have hxi : inner ℝ x ξ ∈ Icc (-1 : ℝ) 1 := abs_le.mp (inner_bound hx hξ)
        have hyi : inner ℝ y ξ ∈ Icc (-1 : ℝ) 1 := abs_le.mp (inner_bound hy hξ)
        have hs := (scalar_strong α hα hα2).2 hxi hyi ha hb hab
        convert! hs using 1 <;> simp [f0, m, inner_add_left, inner_smul_left, inner_sub_left,
          smul_eq_mul, Real.norm_eq_abs, sq_abs, mul_assoc]
      _ = _ := by
        have hsplit := integral_sub ((hi.const_mul a).add (hj.const_mul b)) (hq.const_mul (a * b * (m / 2)))
        simp only [Pi.add_apply] at hsplit
        rw [integral_add (hi.const_mul a) (hj.const_mul b)] at hsplit
        simp only [integral_const_mul] at hsplit
        convert! hsplit using 1
  have hm : 0 ≤ a * b * (m / 2) := by dsimp [m]; positivity
  have hmul := mul_le_mul_of_nonneg_left (hbound (x - y)) hm
  change risk α Γ (a • x + b • y) ≤ a * risk α Γ x + b * risk α Γ y -
    a * b * (c * α * (α - 1) / 2 * ‖x - y‖ ^ 2)
  dsimp [m] at hh hmul
  nlinarith
end ProbMetricStab.Portfolio

open ProbMetricStab.Portfolio

theorem solution {s : ℕ} (Γ : Measure (Rs s)) (hΓ : IsSpectral Γ)
    (hns : Nonsingular Γ) :
    ∀ c : ℝ, 0 < c → (∀ x : Rs s, c * ‖x‖ ^ 2 ≤ ∫ ξ in unitSphere s, |(inner ℝ x ξ : ℝ)| ^ 2 ∂Γ) →
      ∀ α : ℝ, 1 < α → α < 2 → ∃ xs : Rs s, solSet α Γ = {xs} ∧ ∀ x ∈ simplex s,
        (1 / 4) * c * α * (α - 1) * ‖x - xs‖ ^ 2 ≤ risk α Γ x - optVal α Γ := by
  letI := hΓ.1
  have hs : 0 < s := by
    by_contra hn
    have he : s = 0 := by omega
    subst s
    have hempty : unitSphere 0 = ∅ := by
      ext ξ
      have hξ : ξ = 0 := Subsingleton.elim _ _
      simp [unitSphere, hξ]
    have hh := hΓ.2
    simpa [hempty] using hh
  have hnonempty : (simplex s).Nonempty := by
    let i : Fin s := ⟨0, hs⟩
    refine ⟨WithLp.toLp 2 (Pi.single i (1 : ℝ)), ?_⟩
    exact single_mem_stdSimplex ℝ i
  intro c hc hbound α hα hα2
  obtain ⟨xs, hxs, hopt, hmin⟩ := (compact_simplex s).exists_sInf_image_eq_and_le hnonempty
    (continuous_risk Γ hΓ α (by linarith))
  have hstrong := risk_strong Γ hΓ c hc hbound α hα hα2
  have hpos : 0 < c * α * (α - 1) := by positivity
  have hgrowth : ∀ x ∈ simplex s,
      (1 / 4) * c * α * (α - 1) * ‖x - xs‖ ^ 2 ≤ risk α Γ x - risk α Γ xs := by
    intro x hx
    have hmemb := convex_simplex s hx hxs (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    have hmid := hmin _ hmemb
    have hsc := hstrong.2 hx hxs (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    change risk α Γ ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • xs) ≤
      (1 / 2) * risk α Γ x + (1 / 2) * risk α Γ xs -
        (1 / 2) * (1 / 2) * (c * α * (α - 1) / 2 * ‖x - xs‖ ^ 2) at hsc
    nlinarith
  have hsol : solSet α Γ = {xs} := by
    ext y
    constructor
    · intro hy
      have hg := hgrowth y hy.1
      have hm := hy.2 xs hxs
      have hn : ‖y - xs‖ = 0 := by
        have hcoef : 0 < (1 / 4 : ℝ) * c * α * (α - 1) := by positivity
        have hzero := hg.trans (sub_nonpos.mpr hm)
        have hsq : ‖y - xs‖ ^ 2 ≤ 0 := (mul_le_mul_iff_right₀ hcoef).mp (by simpa only [mul_zero] using hzero)
        nlinarith [norm_nonneg (y - xs)]
      exact Set.mem_singleton_iff.mpr (sub_eq_zero.mp (norm_eq_zero.mp hn))
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact ⟨hxs, hmin⟩
  refine ⟨xs, hsol, ?_⟩
  intro x hx
  change _ ≤ risk α Γ x - sInf (risk α Γ '' simplex s)
  rw [hopt]
  exact hgrowth x hx

#print axioms solution

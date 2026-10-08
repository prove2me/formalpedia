-- Prove2me | solution 1 for ZhengQR.EOQHeuristic.cost_formula
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T13:55:29.733255+00:00
-- url     : https://prove2.me/submissions/b7d5c18d-c56f-49da-9968-47bcb67e7e5c

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_costCurves
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel

set_option autoImplicit false

namespace P59e38162

open ZhengQR.EOQHeuristic MeasureTheory

/-! ## Generic convex-function facts -/

lemma tp (G : ℝ → ℝ) (hcv : ConvexOn ℝ Set.univ G) {x z y : ℝ} (hxz : x ≤ z) (hzy : z ≤ y) :
    (y - x) * G z ≤ (y - z) * G x + (z - x) * G y := by
  rcases eq_or_lt_of_le (hxz.trans hzy) with hxy | hxy
  · subst hxy
    have e1 : z = x := le_antisymm hzy hxz
    subst e1
    simp
  · have hyx : 0 < y - x := sub_pos.2 hxy
    have ha : 0 ≤ (y - z) / (y - x) := div_nonneg (by linarith) hyx.le
    have hb : 0 ≤ (z - x) / (y - x) := div_nonneg (by linarith) hyx.le
    have hab : (y - z) / (y - x) + (z - x) / (y - x) = 1 := by
      field_simp; ring
    have key := hcv.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    simp only [smul_eq_mul] at key
    have hpt : (y - z) / (y - x) * x + (z - x) / (y - x) * y = z := by
      field_simp; ring
    rw [hpt] at key
    have := mul_le_mul_of_nonneg_left key hyx.le
    calc (y - x) * G z ≤ (y - x) * ((y - z) / (y - x) * G x + (z - x) / (y - x) * G y) := this
      _ = (y - z) * G x + (z - x) * G y := by field_simp

lemma delta_mono (G : ℝ → ℝ) (hcv : ConvexOn ℝ Set.univ G) {s t Q : ℝ} (hst : s ≤ t)
    (hQ : 0 ≤ Q) : G (s + Q) - G s ≤ G (t + Q) - G t := by
  rcases eq_or_lt_of_le hst with h | h
  · subst h; exact le_refl _
  · have h1 := tp G hcv (x := s) (z := t) (y := t + Q) hst (by linarith)
    have h2 := tp G hcv (x := s) (z := s + Q) (y := t + Q) (by linarith) (by linarith)
    have hL : 0 < t + Q - s := by linarith
    have h3 : (t + Q - s) * (G (s + Q) - G s) ≤ (t + Q - s) * (G (t + Q) - G t) := by
      nlinarith
    exact le_of_mul_le_mul_left h3 hL

lemma outside_left (G : ℝ → ℝ) (hcv : ConvexOn ℝ Set.univ G) {Q r z : ℝ} (hQ : 0 < Q)
    (hb : G (r + Q) = G r) (hz : z ≤ r) : G r ≤ G z := by
  have h1 := tp G hcv (x := z) (z := r) (y := r + Q) hz (by linarith)
  rw [hb] at h1
  have h2 : Q * G r ≤ Q * G z := by nlinarith
  exact le_of_mul_le_mul_left h2 hQ

lemma outside_right (G : ℝ → ℝ) (hcv : ConvexOn ℝ Set.univ G) {Q r z : ℝ} (hQ : 0 < Q)
    (hb : G (r + Q) = G r) (hz : r + Q ≤ z) : G r ≤ G z := by
  have h1 := tp G hcv (x := r) (z := r + Q) (y := z) (by linarith) hz
  rw [hb] at h1
  have h2 : Q * G r ≤ Q * G z := by nlinarith
  exact le_of_mul_le_mul_left h2 hQ

lemma ge_of_win (G : ℝ → ℝ) (hcv : ConvexOn ℝ Set.univ G) {Q r : ℝ} (hQ : 0 < Q)
    (hb : G (r + Q) = G r) (r' : ℝ) : G r ≤ max (G r') (G (r' + Q)) := by
  rcases le_or_gt r' r with h | h
  · exact (outside_left G hcv hQ hb h).trans (le_max_left _ _)
  · exact (outside_right G hcv hQ hb (by linarith)).trans (le_max_right _ _)

/-- strictly inside the window, when the window value exceeds the minimum -/
lemma inside_lt (G : ℝ → ℝ) (hcv : ConvexOn ℝ Set.univ G) {Q r y0 z : ℝ}
    (hb : G (r + Q) = G r) (hy0 : G y0 < G r) (h1 : r < y0) (h2 : y0 < r + Q)
    (hz1 : r < z) (hz2 : z < r + Q) : G z < G r := by
  rcases le_or_gt z y0 with h | h
  · have k := tp G hcv (x := r) (z := z) (y := y0) hz1.le h
    have k2 : (z - r) * G y0 < (z - r) * G r := mul_lt_mul_of_pos_left hy0 (by linarith)
    have k3 : (y0 - r) * G z < (y0 - r) * G r := by nlinarith
    exact lt_of_mul_lt_mul_left k3 (by linarith)
  · have k := tp G hcv (x := y0) (z := z) (y := r + Q) h.le hz2.le
    rw [hb] at k
    have k2 : (r + Q - z) * G y0 < (r + Q - z) * G r := mul_lt_mul_of_pos_left hy0 (by linarith)
    have k3 : (r + Q - y0) * G z < (r + Q - y0) * G r := by nlinarith
    exact lt_of_mul_lt_mul_left k3 (by linarith)

/-! ## The window integral -/

lemma F_deriv (G : ℝ → ℝ) (hc : Continuous G) (Q r : ℝ) :
    HasDerivAt (fun r => ∫ y in r..r + Q, G y) (G (r + Q) - G r) r := by
  have e : (fun r => ∫ y in r..r + Q, G y) =
      fun r => (∫ y in (0:ℝ)..r + Q, G y) - ∫ y in (0:ℝ)..r, G y := by
    funext r
    rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
  rw [e]
  have h1 : HasDerivAt (fun u => ∫ y in (0:ℝ)..u, G y) (G (r + Q)) (r + Q) :=
    (hc.integral_hasStrictDerivAt 0 (r + Q)).hasDerivAt
  have h2 : HasDerivAt (fun u => ∫ y in (0:ℝ)..u, G y) (G r) r :=
    (hc.integral_hasStrictDerivAt 0 r).hasDerivAt
  exact (HasDerivAt.comp_add_const r Q h1).sub h2

lemma balance_of_min (G : ℝ → ℝ) (hc : Continuous G) {Q r : ℝ}
    (hmin : ∀ r', (∫ y in r..r + Q, G y) ≤ ∫ y in r'..r' + Q, G y) : G (r + Q) = G r := by
  have hl : IsLocalMin (fun r => ∫ y in r..r + Q, G y) r := Filter.Eventually.of_forall hmin
  have := hl.hasDerivAt_eq_zero (F_deriv G hc Q r)
  linarith

lemma exists_min (G : ℝ → ℝ) (hc : Continuous G) (hcv : ConvexOn ℝ Set.univ G) {y0 Q : ℝ}
    (hy0 : ∀ z, G y0 ≤ G z) (hQ : 0 ≤ Q) :
    ∃ r, ∀ r', (∫ y in r..r + Q, G y) ≤ ∫ y in r'..r' + Q, G y := by
  have hcont : Continuous (fun s => G (s + Q) - G s) := by fun_prop
  have hIVT := intermediate_value_Icc (by linarith : y0 - Q ≤ y0) hcont.continuousOn
  have h0 : (0:ℝ) ∈ Set.Icc ((fun s => G (s + Q) - G s) (y0 - Q))
      ((fun s => G (s + Q) - G s) y0) := by
    simp only [sub_add_cancel, Set.mem_Icc]
    exact ⟨by linarith [hy0 (y0 - Q)], by linarith [hy0 (y0 + Q)]⟩
  obtain ⟨r0, -, hr0⟩ := hIVT h0
  simp only at hr0
  refine ⟨r0, fun r' => ?_⟩
  have hFc : ContinuousOn (fun r => ∫ y in r..r + Q, G y) Set.univ := fun x _ =>
    (F_deriv G hc Q x).continuousAt.continuousWithinAt
  rcases lt_trichotomy r0 r' with h | h | h
  · obtain ⟨c, hc1, hc2⟩ := exists_hasDerivAt_eq_slope (fun r => ∫ y in r..r + Q, G y)
      (fun r => G (r + Q) - G r) h (hFc.mono (Set.subset_univ _))
      (fun x _ => F_deriv G hc Q x)
    have hd : 0 ≤ G (c + Q) - G c := by
      have := delta_mono G hcv (s := r0) (t := c) hc1.1.le hQ
      linarith
    rw [hc2, le_div_iff₀ (by linarith)] at hd
    linarith
  · rw [h]
  · obtain ⟨c, hc1, hc2⟩ := exists_hasDerivAt_eq_slope (fun r => ∫ y in r..r + Q, G y)
      (fun r => G (r + Q) - G r) h (hFc.mono (Set.subset_univ _))
      (fun x _ => F_deriv G hc Q x)
    have hd : G (c + Q) - G c ≤ 0 := by
      have := delta_mono G hcv (s := c) (t := r0) hc1.2.le hQ
      linarith
    rw [hc2, div_le_iff₀ (by linarith)] at hd
    linarith


section NV

variable {lam L h p : ℝ} {μ : Measure ℝ} (M : IsQRModel lam L h p μ)
include M

lemma integ (y : ℝ) :
    Integrable (fun x => h * max (y - x) 0 + p * max (x - y) 0) μ := by
  have := M.isProb
  have hg : Integrable (fun x => (h + p) * (|y| + |x|)) μ :=
    ((integrable_const |y|).add M.integrable.abs).const_mul (h + p)
  refine hg.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  have hh := M.h_pos
  have hp := M.p_pos
  have a1 : max (y - x) 0 ≤ |y| + |x| :=
    max_le (by linarith [le_abs_self y, neg_abs_le x]) (by positivity)
  have a2 : max (x - y) 0 ≤ |y| + |x| :=
    max_le (by linarith [le_abs_self x, neg_abs_le y]) (by positivity)
  have b1 : 0 ≤ max (y - x) 0 := le_max_right _ _
  have b2 : 0 ≤ max (x - y) 0 := le_max_right _ _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith

lemma nv_slope_r {y1 y2 : ℝ} (h12 : y1 ≤ y2) :
    newsvendorCost μ h p y2 - newsvendorCost μ h p y1 ≤ h * (y2 - y1) := by
  have := M.isProb
  have hh := M.h_pos
  have hp := M.p_pos
  have key : newsvendorCost μ h p y2 ≤
      ∫ x, ((h * max (y1 - x) 0 + p * max (x - y1) 0) + h * (y2 - y1)) ∂μ := by
    unfold newsvendorCost
    refine integral_mono (integ M y2) ((integ M y1).add (integrable_const _)) (fun x => ?_)
    have a1 : max (y2 - x) 0 ≤ max (y1 - x) 0 + (y2 - y1) :=
      max_le (by linarith [le_max_left (y1 - x) 0]) (by linarith [le_max_right (y1 - x) 0])
    have a2 : max (x - y2) 0 ≤ max (x - y1) 0 :=
      max_le (by linarith [le_max_left (x - y1) 0]) (le_max_right _ _)
    simp only
    nlinarith
  rw [integral_add (integ M y1) (integrable_const _), integral_const, probReal_univ,
    one_smul] at key
  unfold newsvendorCost at key ⊢
  linarith

lemma nv_slope_l {y1 y2 : ℝ} (h12 : y1 ≤ y2) :
    newsvendorCost μ h p y1 - newsvendorCost μ h p y2 ≤ p * (y2 - y1) := by
  have := M.isProb
  have hh := M.h_pos
  have hp := M.p_pos
  have key : newsvendorCost μ h p y1 ≤
      ∫ x, ((h * max (y2 - x) 0 + p * max (x - y2) 0) + p * (y2 - y1)) ∂μ := by
    unfold newsvendorCost
    refine integral_mono (integ M y1) ((integ M y2).add (integrable_const _)) (fun x => ?_)
    have a1 : max (x - y1) 0 ≤ max (x - y2) 0 + (y2 - y1) :=
      max_le (by linarith [le_max_left (x - y2) 0]) (by linarith [le_max_right (x - y2) 0])
    have a2 : max (y1 - x) 0 ≤ max (y2 - x) 0 :=
      max_le (by linarith [le_max_left (y2 - x) 0]) (le_max_right _ _)
    simp only
    nlinarith
  rw [integral_add (integ M y2) (integrable_const _), integral_const, probReal_univ,
    one_smul] at key
  unfold newsvendorCost at key ⊢
  linarith

lemma nv_convex : ConvexOn ℝ Set.univ (newsvendorCost μ h p) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hh := M.h_pos
  have hp := M.p_pos
  simp only [smul_eq_mul]
  unfold newsvendorCost
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((integ M x).const_mul a) ((integ M y).const_mul b)]
  refine integral_mono (integ M _) (((integ M x).const_mul a).add ((integ M y).const_mul b))
    (fun t => ?_)
  have a1 : max (a * x + b * y - t) 0 ≤ a * max (x - t) 0 + b * max (y - t) 0 := by
    apply max_le
    · have e : a * x + b * y - t = a * (x - t) + b * (y - t) := by
        linear_combination t * hab
      rw [e]
      exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
    · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))
  have a2 : max (t - (a * x + b * y)) 0 ≤ a * max (t - x) 0 + b * max (t - y) 0 := by
    apply max_le
    · have e : t - (a * x + b * y) = a * (t - x) + b * (t - y) := by
        linear_combination (-t) * hab
      rw [e]
      exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
    · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))
  simp only
  nlinarith [mul_le_mul_of_nonneg_left a1 hh.le, mul_le_mul_of_nonneg_left a2 hp.le]

lemma nv_cont : Continuous (newsvendorCost μ h p) := by
  have hh := M.h_pos
  have hp := M.p_pos
  refine (LipschitzWith.of_le_add_mul' (h + p) (fun x y => ?_)).continuous
  rw [Real.dist_eq]
  rcases le_total y x with hxy | hxy
  · have := nv_slope_r M hxy
    have : h * (x - y) ≤ (h + p) * |x - y| := by
      rw [abs_of_nonneg (by linarith)]; nlinarith
    linarith
  · have := nv_slope_l M hxy
    have : p * (y - x) ≤ (h + p) * |x - y| := by
      rw [abs_of_nonpos (by linarith)]; nlinarith
    linarith

lemma nv_lb (y : ℝ) :
    h * (y - lam * L) ≤ newsvendorCost μ h p y ∧
      p * (lam * L - y) ≤ newsvendorCost μ h p y := by
  have := M.isProb
  have hh := M.h_pos
  have hp := M.p_pos
  have i1 : Integrable (fun x => h * y - h * x) μ :=
    (integrable_const _).sub (M.integrable.const_mul _)
  have i2 : Integrable (fun x => p * x - p * y) μ :=
    (M.integrable.const_mul _).sub (integrable_const _)
  have e1 : ∫ x, (h * y - h * x) ∂μ = h * (y - lam * L) := by
    rw [integral_sub (integrable_const _) (M.integrable.const_mul _), integral_const,
      probReal_univ, one_smul, integral_const_mul, M.mean]
    ring
  have e2 : ∫ x, (p * x - p * y) ∂μ = p * (lam * L - y) := by
    rw [integral_sub (M.integrable.const_mul _) (integrable_const _), integral_const,
      probReal_univ, one_smul, integral_const_mul, M.mean]
    ring
  constructor
  · rw [← e1]
    unfold newsvendorCost
    refine integral_mono i1 (integ M y) (fun x => ?_)
    have b1 := le_max_left (y - x) 0
    have b2 : 0 ≤ max (x - y) 0 := le_max_right _ _
    simp only
    nlinarith
  · rw [← e2]
    unfold newsvendorCost
    refine integral_mono i2 (integ M y) (fun x => ?_)
    have b1 := le_max_left (x - y) 0
    have b2 : 0 ≤ max (y - x) 0 := le_max_right _ _
    simp only
    nlinarith

end NV

lemma opt_iff (G : ℝ → ℝ) (lam K Q r : ℝ) (hQ : 0 < Q) :
    IsOptReorder G lam K Q r ↔ ∀ r', (∫ y in r..r + Q, G y) ≤ ∫ y in r'..r' + Q, G y := by
  unfold IsOptReorder qrCost
  simp only [div_le_div_iff_of_pos_right hQ, add_le_add_iff_left]

lemma rp_spec (G : ℝ → ℝ) (hc : Continuous G) (hcv : ConvexOn ℝ Set.univ G) {y0 : ℝ}
    (hy0 : ∀ z, G y0 ≤ G z) (lam K Q : ℝ) (hQ : 0 < Q) :
    G (reorderPt G lam K Q + Q) = G (reorderPt G lam K Q) := by
  obtain ⟨r0, hr0⟩ := exists_min G hc hcv hy0 hQ.le
  have hex : ∃ r, IsOptReorder G lam K Q r := ⟨r0, (opt_iff G lam K Q r0 hQ).2 hr0⟩
  have hspec : IsOptReorder G lam K Q (reorderPt G lam K Q) := by
    unfold reorderPt; rw [dif_pos hex]; exact hex.choose_spec
  exact balance_of_min G hc ((opt_iff G lam K Q _ hQ).1 hspec)

lemma rp_indep (G : ℝ → ℝ) (lam K K' Q : ℝ) (hQ : 0 < Q) :
    reorderPt G lam K Q = reorderPt G lam K' Q := by
  have e : IsOptReorder G lam K Q = IsOptReorder G lam K' Q :=
    funext fun r => propext ((opt_iff G lam K Q r hQ).trans (opt_iff G lam K' Q r hQ).symm)
  unfold reorderPt
  rw [e]

lemma minPt_eq (G : ℝ → ℝ) {y0 : ℝ} (hy0 : ∀ z, G y0 ≤ G z)
    (hu : ∀ y, (∀ z, G y ≤ G z) → y = y0) : minPt G = y0 := by
  have hex : ∃ y, ∀ z, G y ≤ G z := ⟨y0, hy0⟩
  apply hu
  unfold minPt; rw [dif_pos hex]; exact hex.choose_spec

lemma strict_right (G : ℝ → ℝ) (hcv : ConvexOn ℝ Set.univ G) {y0 a b : ℝ}
    (hb : G y0 < G b) (ha : y0 ≤ a) (hab : a < b) : G a < G b := by
  have k := tp G hcv (x := y0) (z := a) (y := b) ha hab.le
  have k2 : (b - a) * G y0 < (b - a) * G b := mul_lt_mul_of_pos_left hb (by linarith)
  have k3 : (b - y0) * G a < (b - y0) * G b := by nlinarith
  exact lt_of_mul_lt_mul_left k3 (by linarith)

lemma strict_left (G : ℝ → ℝ) (hcv : ConvexOn ℝ Set.univ G) {y0 a b : ℝ}
    (ha : G y0 < G a) (hab : a < b) (hb : b ≤ y0) : G b < G a := by
  have k := tp G hcv (x := a) (z := b) (y := y0) hab.le hb
  have k2 : (b - a) * G y0 < (b - a) * G a := mul_lt_mul_of_pos_left ha (by linarith)
  have k3 : (y0 - a) * G b < (y0 - a) * G a := by nlinarith
  exact lt_of_mul_lt_mul_left k3 (by linarith)



/-! ## Envelope identity -/

lemma inside_le (G : ℝ → ℝ) (hcv : ConvexOn ℝ Set.univ G) {Q r z : ℝ} (hQ : 0 < Q)
    (hb : G (r + Q) = G r) (h1 : r ≤ z) (h2 : z ≤ r + Q) : G z ≤ G r := by
  have k := tp G hcv (x := r) (z := z) (y := r + Q) h1 h2
  rw [hb] at k
  have k2 : Q * G z ≤ Q * G r := by nlinarith
  exact le_of_mul_le_mul_left k2 hQ

lemma int_bounds (G : ℝ → ℝ) (hc : Continuous G) {α β lo hi : ℝ} (hab : α ≤ β)
    (hlo : ∀ z ∈ Set.Icc α β, lo ≤ G z) (hhi : ∀ z ∈ Set.Icc α β, G z ≤ hi) :
    (β - α) * lo ≤ (∫ y in α..β, G y) ∧ (∫ y in α..β, G y) ≤ (β - α) * hi := by
  constructor
  · have := intervalIntegral.integral_mono_on hab
      (intervalIntegrable_const : IntervalIntegrable (fun _ => lo) MeasureTheory.volume α β)
      (hc.intervalIntegrable α β) hlo
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    exact this
  · have := intervalIntegral.integral_mono_on hab (hc.intervalIntegrable α β)
      (intervalIntegrable_const : IntervalIntegrable (fun _ => hi) MeasureTheory.volume α β) hhi
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    exact this

lemma W_step (G : ℝ → ℝ) (hc : Continuous G) (hcv : ConvexOn ℝ Set.univ G) {a b ra rb : ℝ}
    (ha : 0 < a) (hab : a < b) (bala : G (ra + a) = G ra) (balb : G (rb + b) = G rb)
    (n1 : rb < ra) (n2 : ra + a < rb + b) :
    (b - a) * G ra ≤ (∫ y in rb..rb + b, G y) - ∫ y in ra..ra + a, G y ∧
      (∫ y in rb..rb + b, G y) - (∫ y in ra..ra + a, G y) ≤ (b - a) * G rb := by
  have hb : 0 < b := ha.trans hab
  have split : (∫ y in rb..ra, G y) + (∫ y in ra..ra + a, G y) + (∫ y in ra + a..rb + b, G y)
      = ∫ y in rb..rb + b, G y := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)]
  obtain ⟨p1, p2⟩ := int_bounds G hc (lo := G ra) (hi := G rb) n1.le
    (fun z hz => outside_left G hcv ha bala hz.2)
    (fun z hz => inside_le G hcv hb balb hz.1 (by linarith [hz.2]))
  obtain ⟨q1, q2⟩ := int_bounds G hc (lo := G ra) (hi := G rb) n2.le
    (fun z hz => outside_right G hcv ha bala hz.1)
    (fun z hz => inside_le G hcv hb balb (by linarith [hz.1]) hz.2)
  have e : (b - a) = (ra - rb) + (rb + b - (ra + a)) := by ring
  rw [← split, e]
  constructor <;> nlinarith

lemma tele (E H : ℝ → ℝ) {Q : ℝ} (hQ : 0 ≤ Q)
    (hE : ∀ a b, 0 ≤ a → a ≤ b → |E b - E a| ≤ (b - a) * (H b - H a)) (n : ℕ) (hn : 0 < n) :
    |E Q - E 0| ≤ Q / n * (H Q - H 0) := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set x : ℕ → ℝ := fun i => Q / n * i with hx
  have hx0 : x 0 = 0 := by simp [x]
  have hxn : x n = Q := by simp only [x]; field_simp
  have hsum : E Q - E 0 = ∑ i ∈ Finset.range n, (E (x (i + 1)) - E (x i)) := by
    rw [Finset.sum_range_sub (fun i => E (x i)), hxn, hx0]
  have hsum2 : H Q - H 0 = ∑ i ∈ Finset.range n, (H (x (i + 1)) - H (x i)) := by
    rw [Finset.sum_range_sub (fun i => H (x i)), hxn, hx0]
  rw [hsum, hsum2, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have hstep : x (i + 1) - x i = Q / n := by simp only [x]; push_cast; ring
  have hq : 0 ≤ Q / n := div_nonneg hQ hnr.le
  have h0 : 0 ≤ x i := by simp only [x]; positivity
  have h1 : x i ≤ x (i + 1) := by linarith
  have := hE (x i) (x (i + 1)) h0 h1
  rw [hstep] at this
  exact this

lemma eq_of_tele {d Q c : ℝ} (hb : ∀ n : ℕ, 0 < n → |d| ≤ Q / n * c) : d = 0 := by
  by_contra hne
  have hpos : 0 < |d| := abs_pos.2 hne
  obtain ⟨n, hn⟩ := exists_nat_gt (Q * c / |d|)
  have h1 := hb (n + 1) (Nat.succ_pos n)
  have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [show Q / ((n + 1 : ℕ) : ℝ) * c = Q * c / ((n : ℝ) + 1) by push_cast; ring,
    le_div_iff₀ hm] at h1
  rw [div_lt_iff₀ hpos] at hn
  nlinarith

end P59e38162

open ZhengQR.EOQHeuristic MeasureTheory Filter Topology in
theorem solution {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) (Q : ℝ) (hQ : 0 < Q) :
    (∫ y in reorderPt (newsvendorCost μ h p) lam K Q..reorderPt (newsvendorCost μ h p) lam K Q + Q, newsvendorCost μ h p y) = ∫ y in (0 : ℝ)..Q, hFun (newsvendorCost μ h p) lam K y ∧
      optCost (newsvendorCost μ h p) lam K Q = (lam * K + ∫ y in (0 : ℝ)..Q, hFun (newsvendorCost μ h p) lam K y) / Q := by
  set G := newsvendorCost μ h p with hGdef
  have hc : Continuous G := P59e38162.nv_cont hM
  have hcv : ConvexOn ℝ Set.univ G := P59e38162.nv_convex hM
  obtain ⟨y0, hy0, huniq⟩ := hM.unique_min
  have hu : ∀ y, (∀ z, G y ≤ G z) → y = y0 := huniq
  have hmin : minPt G = y0 := P59e38162.minPt_eq G hy0 hu
  have hstr : ∀ a, a ≠ y0 → G y0 < G a := by
    intro a ha
    rcases lt_or_ge (G y0) (G a) with h1 | h1
    · exact h1
    · exact absurd (hu a fun z => h1.trans (hy0 z)) ha
  set r := reorderPt G lam K with hr
  have bal : ∀ q, 0 < q → G (r q + q) = G (r q) := fun q hq =>
    P59e38162.rp_spec G hc hcv hy0 lam K q hq
  have pos : ∀ q, 0 < q → r q < y0 ∧ y0 < r q + q := by
    intro q hq
    have e := bal q hq
    have hlt : G y0 < G (r q) := by
      rcases eq_or_ne (r q) y0 with h1 | h1
      · have h2 : r q + q ≠ y0 := by rw [h1]; linarith
        have := hstr _ h2
        rw [e] at this; exact this
      · exact hstr _ h1
    constructor
    · by_contra hcon
      have := P59e38162.outside_left G hcv hq e (not_lt.1 hcon)
      linarith
    · by_contra hcon
      have := P59e38162.outside_right G hcv hq e (not_lt.1 hcon)
      linarith
  have nest : ∀ a b, 0 < a → a < b → r b < r a ∧ r a + a < r b + b := by
    intro a b ha hab
    have hb : 0 < b := ha.trans hab
    obtain ⟨a1, a2⟩ := pos a ha
    obtain ⟨b1, b2⟩ := pos b hb
    have e := bal a ha
    have e' := bal b hb
    constructor
    · by_contra hcon
      have hle : r a ≤ r b := not_lt.1 hcon
      have g1 : G (r b) ≤ G (r a) := by
        rcases eq_or_lt_of_le hle with h1 | h1
        · rw [h1]
        · exact (P59e38162.strict_left G hcv (hstr _ (ne_of_lt a1)) h1 b1.le).le
      have g2 : G (r a + a) < G (r b + b) :=
        P59e38162.strict_right G hcv (hstr _ (ne_of_gt (by linarith))) a2.le (by linarith)
      linarith
    · by_contra hcon
      have hle : r b + b ≤ r a + a := not_lt.1 hcon
      have g1 : G (r a) < G (r b) :=
        P59e38162.strict_left G hcv (hstr _ (ne_of_lt (by linarith))) (by linarith) a1.le
      have g2 : G (r b + b) ≤ G (r a + a) := by
        rcases eq_or_lt_of_le hle with h1 | h1
        · rw [h1]
        · exact (P59e38162.strict_right G hcv (hstr _ (ne_of_gt a2)) b2.le h1).le
      linarith
  set H := hFun G lam K with hHdef
  have Hpos : ∀ q, 0 < q → H q = G (r q) := fun q hq => by
    show hFun G lam K q = G (reorderPt G lam K q)
    rw [hFun, if_pos hq]
  have H0 : H 0 = G y0 := by simp only [hHdef, hFun, lt_irrefl, if_false, hmin]
  set W : ℝ → ℝ := fun q => ∫ y in r q..r q + q, G y with hW
  have W0 : W 0 = 0 := by simp only [hW, add_zero, intervalIntegral.integral_same]
  have Wb : ∀ a b, 0 ≤ a → a < b → (b - a) * H a ≤ W b - W a ∧ W b - W a ≤ (b - a) * H b := by
    intro a b ha hab
    have hb : 0 < b := lt_of_le_of_lt ha hab
    rw [Hpos b hb]
    rcases eq_or_lt_of_le ha with h0 | h0
    · subst h0
      rw [H0, W0, sub_zero, sub_zero]
      obtain ⟨b1, b2⟩ := pos b hb
      have := P59e38162.int_bounds G hc (α := r b) (β := r b + b) (lo := G y0) (hi := G (r b))
        (by linarith) (fun z _ => hy0 z)
        (fun z hz => P59e38162.inside_le G hcv hb (bal b hb) hz.1 hz.2)
      simp only [add_sub_cancel_left] at this
      exact this
    · rw [Hpos a h0]
      obtain ⟨n1, n2⟩ := nest a b h0 hab
      exact P59e38162.W_step G hc hcv h0 hab (bal a h0) (bal b hb) n1 n2
  have Hmono : MonotoneOn H (Set.Ici 0) := by
    intro a ha b hb hab
    rcases eq_or_lt_of_le hab with h1 | h1
    · rw [h1]
    · obtain ⟨w1, w2⟩ := Wb a b ha h1
      have : (b - a) * H a ≤ (b - a) * H b := w1.trans w2
      exact le_of_mul_le_mul_left this (by linarith)
  have Hint : ∀ a b, 0 ≤ a → a ≤ b → IntervalIntegrable H volume a b := by
    intro a b ha hab
    apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact Hmono.mono fun z hz => le_trans ha hz.1
  set I : ℝ → ℝ := fun q => ∫ y in (0 : ℝ)..q, H y with hI
  have I0 : I 0 = 0 := by simp only [hI, intervalIntegral.integral_same]
  have Ib : ∀ a b, 0 ≤ a → a ≤ b → (b - a) * H a ≤ I b - I a ∧ I b - I a ≤ (b - a) * H b := by
    intro a b ha hab
    have e : I b - I a = ∫ y in a..b, H y :=
      intervalIntegral.integral_interval_sub_left (Hint 0 b le_rfl (ha.trans hab))
        (Hint 0 a le_rfl ha)
    rw [e]
    constructor
    · have := intervalIntegral.integral_mono_on hab intervalIntegrable_const (Hint a b ha hab)
        (fun z hz => Hmono ha (le_trans ha hz.1) hz.1)
      rw [intervalIntegral.integral_const, smul_eq_mul] at this
      exact this
    · have := intervalIntegral.integral_mono_on hab (Hint a b ha hab) intervalIntegrable_const
        (fun z hz => Hmono (le_trans ha hz.1) (le_trans ha hab) hz.2)
      rw [intervalIntegral.integral_const, smul_eq_mul] at this
      exact this
  have hE : ∀ a b, 0 ≤ a → a ≤ b →
      |(W b - I b) - (W a - I a)| ≤ (b - a) * (H b - H a) := by
    intro a b ha hab
    rcases eq_or_lt_of_le hab with h1 | h1
    · subst h1; simp
    · obtain ⟨w1, w2⟩ := Wb a b ha h1
      obtain ⟨i1, i2⟩ := Ib a b ha hab
      rw [mul_sub]
      exact abs_le.2 ⟨by linarith, by linarith⟩
  have key : (W Q - I Q) - (W 0 - I 0) = 0 :=
    P59e38162.eq_of_tele (Q := Q) (c := H Q - H 0) fun n hn =>
      P59e38162.tele (fun q => W q - I q) H hQ.le hE n hn
  rw [W0, I0] at key
  have conj0 : W Q = I Q := by linarith
  have conj1 : (∫ y in r Q..r Q + Q, G y) = ∫ y in (0 : ℝ)..Q, H y := conj0
  refine ⟨conj1, ?_⟩
  show (lam * K + ∫ y in r Q..r Q + Q, G y) / Q = (lam * K + ∫ y in (0 : ℝ)..Q, H y) / Q
  rw [conj1]

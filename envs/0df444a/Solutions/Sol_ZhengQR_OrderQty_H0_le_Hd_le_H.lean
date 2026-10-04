-- Prove2me | solution 1 for ZhengQR.OrderQty.H0_le_Hd_le_H
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T10:23:18.405952+00:00
-- url     : https://prove2.me/submissions/d75c76d4-b2c4-48cf-965c-1c1672e46e76

import Mathlib
import Definitions.Def_ZhengQR_OrderQty_newsvendorCost
import Definitions.Def_ZhengQR_OrderQty_qrMachinery

set_option autoImplicit false

namespace P25e96b3b

open ZhengQR.OrderQty MeasureTheory

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


lemma H_pos (G : ℝ → ℝ) (hc : Continuous G) (hcv : ConvexOn ℝ Set.univ G) {y0 : ℝ}
    (hy0 : ∀ z, G y0 ≤ G z) (Q : ℝ) (hQ : 0 < Q) :
    Hfun G Q = G (optReorder G Q) ∧
      G (optReorder G Q + Q) = G (optReorder G Q) := by
  have hex := exists_min G hc hcv hy0 hQ.le
  have hspec : ∀ r', (∫ y in optReorder G Q..optReorder G Q + Q, G y) ≤
      ∫ y in r'..r' + Q, G y := by
    unfold optReorder; rw [dif_pos hex]; exact hex.choose_spec
  refine ⟨?_, balance_of_min G hc hspec⟩
  unfold Hfun; rw [if_pos hQ]

lemma minPoint_spec (G : ℝ → ℝ) {y0 : ℝ} (hy0 : ∀ z, G y0 ≤ G z) :
    ∀ z, G (minPoint G) ≤ G z := by
  have hex : ∃ y, IsMinimizer G y := ⟨y0, hy0⟩
  unfold minPoint; rw [dif_pos hex]; exact hex.choose_spec

lemma H_zero (G : ℝ → ℝ) : Hfun G 0 = G (minPoint G) := by
  unfold Hfun; rw [if_neg (lt_irrefl 0)]

lemma Hwin (G : ℝ → ℝ) (hc : Continuous G) (hcv : ConvexOn ℝ Set.univ G) {y0 : ℝ}
    (hy0 : ∀ z, G y0 ≤ G z) (Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ r, Hfun G Q = G r ∧ G (r + Q) = G r := by
  rcases eq_or_lt_of_le hQ with h | h
  · subst h
    exact ⟨minPoint G, H_zero G, by rw [add_zero]⟩
  · exact ⟨_, H_pos G hc hcv hy0 Q h⟩

lemma Hle (G : ℝ → ℝ) (hc : Continuous G) (hcv : ConvexOn ℝ Set.univ G) {y0 : ℝ}
    (hy0 : ∀ z, G y0 ≤ G z) (Q : ℝ) (hQ : 0 ≤ Q) (r : ℝ) :
    Hfun G Q ≤ max (G r) (G (r + Q)) := by
  rcases eq_or_lt_of_le hQ with h | h
  · subst h
    rw [H_zero]
    exact (minPoint_spec G hy0 r).trans (le_max_left _ _)
  · obtain ⟨e1, e2⟩ := H_pos G hc hcv hy0 Q h
    rw [e1]
    exact ge_of_win G hcv h e2 r

/-! ## The newsvendor cost -/

section NV

variable {lam L h p : ℝ} {μ : Measure ℝ}

lemma integ (hh : 0 < h) (hp : 0 < p) (hμ : IsLeadtimeDemand lam L μ) (y : ℝ) :
    Integrable (fun x => h * max (y - x) 0 + p * max (x - y) 0) μ := by
  have := hμ.isProb
  have hg : Integrable (fun x => (h + p) * (|y| + |x|)) μ :=
    ((integrable_const |y|).add hμ.integrable.abs).const_mul (h + p)
  refine hg.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  have a1 : max (y - x) 0 ≤ |y| + |x| :=
    max_le (by linarith [le_abs_self y, neg_abs_le x]) (by positivity)
  have a2 : max (x - y) 0 ≤ |y| + |x| :=
    max_le (by linarith [le_abs_self x, neg_abs_le y]) (by positivity)
  have b1 : 0 ≤ max (y - x) 0 := le_max_right _ _
  have b2 : 0 ≤ max (x - y) 0 := le_max_right _ _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith

lemma nv_slope_r (hh : 0 < h) (hp : 0 < p) (hμ : IsLeadtimeDemand lam L μ) {y1 y2 : ℝ} (h12 : y1 ≤ y2) :
    newsvendorCost h p μ y2 - newsvendorCost h p μ y1 ≤ h * (y2 - y1) := by
  have := hμ.isProb
  have key : newsvendorCost h p μ y2 ≤
      ∫ x, ((h * max (y1 - x) 0 + p * max (x - y1) 0) + h * (y2 - y1)) ∂μ := by
    unfold newsvendorCost
    refine integral_mono (integ hh hp hμ y2) ((integ hh hp hμ y1).add (integrable_const _)) (fun x => ?_)
    have a1 : max (y2 - x) 0 ≤ max (y1 - x) 0 + (y2 - y1) :=
      max_le (by linarith [le_max_left (y1 - x) 0]) (by linarith [le_max_right (y1 - x) 0])
    have a2 : max (x - y2) 0 ≤ max (x - y1) 0 :=
      max_le (by linarith [le_max_left (x - y1) 0]) (le_max_right _ _)
    simp only
    nlinarith
  rw [integral_add (integ hh hp hμ y1) (integrable_const _), integral_const, probReal_univ,
    one_smul] at key
  unfold newsvendorCost at key ⊢
  linarith

lemma nv_slope_l (hh : 0 < h) (hp : 0 < p) (hμ : IsLeadtimeDemand lam L μ) {y1 y2 : ℝ} (h12 : y1 ≤ y2) :
    newsvendorCost h p μ y1 - newsvendorCost h p μ y2 ≤ p * (y2 - y1) := by
  have := hμ.isProb
  have key : newsvendorCost h p μ y1 ≤
      ∫ x, ((h * max (y2 - x) 0 + p * max (x - y2) 0) + p * (y2 - y1)) ∂μ := by
    unfold newsvendorCost
    refine integral_mono (integ hh hp hμ y1) ((integ hh hp hμ y2).add (integrable_const _)) (fun x => ?_)
    have a1 : max (x - y1) 0 ≤ max (x - y2) 0 + (y2 - y1) :=
      max_le (by linarith [le_max_left (x - y2) 0]) (by linarith [le_max_right (x - y2) 0])
    have a2 : max (y1 - x) 0 ≤ max (y2 - x) 0 :=
      max_le (by linarith [le_max_left (y2 - x) 0]) (le_max_right _ _)
    simp only
    nlinarith
  rw [integral_add (integ hh hp hμ y2) (integrable_const _), integral_const, probReal_univ,
    one_smul] at key
  unfold newsvendorCost at key ⊢
  linarith

lemma nv_convex (hh : 0 < h) (hp : 0 < p) (hμ : IsLeadtimeDemand lam L μ) : ConvexOn ℝ Set.univ (newsvendorCost h p μ) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  unfold newsvendorCost
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((integ hh hp hμ x).const_mul a) ((integ hh hp hμ y).const_mul b)]
  refine integral_mono (integ hh hp hμ _) (((integ hh hp hμ x).const_mul a).add ((integ hh hp hμ y).const_mul b))
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

lemma nv_cont (hh : 0 < h) (hp : 0 < p) (hμ : IsLeadtimeDemand lam L μ) : Continuous (newsvendorCost h p μ) := by
  refine (LipschitzWith.of_le_add_mul' (h + p) (fun x y => ?_)).continuous
  rw [Real.dist_eq]
  rcases le_total y x with hyx | hyx
  · have := nv_slope_r hh hp hμ hyx
    have : h * (x - y) ≤ (h + p) * |x - y| := by
      rw [abs_of_nonneg (by linarith)]; nlinarith
    linarith
  · have := nv_slope_l hh hp hμ hyx
    have : p * (y - x) ≤ (h + p) * |x - y| := by
      rw [abs_of_nonpos (by linarith)]; nlinarith
    linarith

lemma nv_lb (hh : 0 < h) (hp : 0 < p) (hμ : IsLeadtimeDemand lam L μ) (y : ℝ) :
    h * (y - lam * L) ≤ newsvendorCost h p μ y ∧
      p * (lam * L - y) ≤ newsvendorCost h p μ y := by
  have := hμ.isProb
  have i1 : Integrable (fun x => h * y - h * x) μ :=
    (integrable_const _).sub (hμ.integrable.const_mul _)
  have i2 : Integrable (fun x => p * x - p * y) μ :=
    (hμ.integrable.const_mul _).sub (integrable_const _)
  have e1 : ∫ x, (h * y - h * x) ∂μ = h * (y - lam * L) := by
    rw [integral_sub (integrable_const _) (hμ.integrable.const_mul _), integral_const,
      probReal_univ, one_smul, integral_const_mul, hμ.mean_eq]
    ring
  have e2 : ∫ x, (p * x - p * y) ∂μ = p * (lam * L - y) := by
    rw [integral_sub (hμ.integrable.const_mul _) (integrable_const _), integral_const,
      probReal_univ, one_smul, integral_const_mul, hμ.mean_eq]
    ring
  constructor
  · rw [← e1]
    unfold newsvendorCost
    refine integral_mono i1 (integ hh hp hμ y) (fun x => ?_)
    have b1 := le_max_left (y - x) 0
    have b2 : 0 ≤ max (x - y) 0 := le_max_right _ _
    simp only
    nlinarith
  · rw [← e2]
    unfold newsvendorCost
    refine integral_mono i2 (integ hh hp hμ y) (fun x => ?_)
    have b1 := le_max_left (x - y) 0
    have b2 : 0 ≤ max (y - x) 0 := le_max_right _ _
    simp only
    nlinarith

end NV


section EOQ

variable {lam L h p : ℝ} {μ : Measure ℝ}

lemma gd_cont : Continuous (eoqCost lam L h p) := by
  unfold eoqCost
  exact (continuous_const.mul ((continuous_id.sub continuous_const).max continuous_const)).add
    (continuous_const.mul ((continuous_const.sub continuous_id).max continuous_const))

lemma gd_convex (hh : 0 < h) (hp : 0 < p) : ConvexOn ℝ Set.univ (eoqCost lam L h p) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  unfold eoqCost
  set t := lam * L
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
  nlinarith [mul_le_mul_of_nonneg_left a1 hh.le, mul_le_mul_of_nonneg_left a2 hp.le]

lemma gd_min (hh : 0 < h) (hp : 0 < p) : ∀ z, eoqCost lam L h p (lam * L) ≤ eoqCost lam L h p z := by
  intro z
  unfold eoqCost
  simp only [sub_self, max_self, mul_zero, add_zero]
  have b1 : 0 ≤ max (z - lam * L) 0 := le_max_right _ _
  have b2 : 0 ≤ max (lam * L - z) 0 := le_max_right _ _
  positivity

lemma Hd_eq (hh : 0 < h) (hp : 0 < p) (Q : ℝ) (hQ : 0 ≤ Q) : Hfun (eoqCost lam L h p) Q = h * p / (h + p) * Q := by
  have hhp : 0 < h + p := add_pos hh hp
  set Gd := eoqCost lam L h p with hGd
  have hHd : Hfun (eoqCost lam L h p) Q = Hfun Gd Q := rfl
  set m := lam * L with hm
  apply le_antisymm
  · have k := Hle Gd (gd_cont) (gd_convex hh hp) (gd_min hh hp) Q hQ
      (m - h * Q / (h + p))
    have u1 : 0 ≤ h * Q / (h + p) := by positivity
    have u2 : 0 ≤ p * Q / (h + p) := by positivity
    have hpt : m - h * Q / (h + p) + Q = m + p * Q / (h + p) := by
      field_simp; ring
    have v1 : Gd (m - h * Q / (h + p)) = h * p / (h + p) * Q := by
      rw [hGd]; unfold eoqCost; rw [← hm]
      rw [max_eq_right (by linarith), max_eq_left (by linarith)]
      field_simp; ring
    have v2 : Gd (m + p * Q / (h + p)) = h * p / (h + p) * Q := by
      rw [hGd]; unfold eoqCost; rw [← hm]
      rw [max_eq_left (by linarith), max_eq_right (by linarith)]
      field_simp; ring
    rw [hpt, v1, v2, max_self] at k
    rw [hHd]; exact k
  · obtain ⟨r, e1, e2⟩ := Hwin Gd (gd_cont) (gd_convex hh hp) (gd_min hh hp) Q hQ
    have l1 : h * (r + Q - m) ≤ Gd (r + Q) := by
      rw [hGd]; unfold eoqCost; rw [← hm]
      have := le_max_left (r + Q - m) 0
      have := le_max_right (m - (r + Q)) 0
      nlinarith
    have l2 : p * (m - r) ≤ Gd r := by
      rw [hGd]; unfold eoqCost; rw [← hm]
      have := le_max_left (m - r) 0
      have := le_max_right (r - m) 0
      nlinarith
    rw [e2] at l1
    rw [hHd, e1, div_mul_eq_mul_div, div_le_iff₀ hhp]
    nlinarith

lemma H_facts (hh : 0 < h) (hp : 0 < p) (hμ : IsLeadtimeDemand lam L μ)
    (hG : ∃! y : ℝ, IsMinimizer (newsvendorCost h p μ) y) :
    StrictMonoOn (Hfun (newsvendorCost h p μ)) (Set.Ici 0) ∧
      (∀ Q₁ Q₂ : ℝ, 0 ≤ Q₁ → Q₁ ≤ Q₂ →
        Hfun (newsvendorCost h p μ) Q₂ - Hfun (newsvendorCost h p μ) Q₁ ≤ h * p / (h + p) * (Q₂ - Q₁)) ∧
      (∀ Q, 0 ≤ Q → h * p / (h + p) * Q ≤ Hfun (newsvendorCost h p μ) Q) := by
  set G := newsvendorCost h p μ with hGdef
  have hH : ∀ Q, Hfun (newsvendorCost h p μ) Q = Hfun G Q := fun Q => rfl
  have hc : Continuous G := nv_cont hh hp hμ
  have hcv : ConvexOn ℝ Set.univ G := nv_convex hh hp hμ
  obtain ⟨y0, hy0, huniq⟩ := hG
  have hhp : 0 < h + p := add_pos hh hp
  have win := Hwin G hc hcv hy0
  have hle := Hle G hc hcv hy0
  -- chord bound
  have chord : ∀ Q₁ Q₂ : ℝ, 0 ≤ Q₁ → Q₁ ≤ Q₂ →
      Hfun (newsvendorCost h p μ) Q₂ - Hfun (newsvendorCost h p μ) Q₁ ≤ h * p / (h + p) * (Q₂ - Q₁) := by
    intro Q₁ Q₂ hQ1 hQ12
    obtain ⟨r1, e1, e2⟩ := win Q₁ hQ1
    set d := Q₂ - Q₁ with hd
    have hd0 : 0 ≤ d := by linarith
    have k := hle Q₂ (by linarith) (r1 - h * d / (h + p))
    have hpt : r1 - h * d / (h + p) + Q₂ = (r1 + Q₁) + p * d / (h + p) := by
      field_simp; rw [hd]; ring
    rw [hpt] at k
    have s1 := nv_slope_l hh hp hμ
      (show r1 - h * d / (h + p) ≤ r1 by
        have : 0 ≤ h * d / (h + p) := by positivity
        linarith)
    have s2 := nv_slope_r hh hp hμ
      (show r1 + Q₁ ≤ (r1 + Q₁) + p * d / (h + p) by
        have : 0 ≤ p * d / (h + p) := by positivity
        linarith)
    have c1 : p * (r1 - (r1 - h * d / (h + p))) = h * p / (h + p) * d := by
      field_simp; ring
    have c2 : h * ((r1 + Q₁) + p * d / (h + p) - (r1 + Q₁)) =
        h * p / (h + p) * d := by
      field_simp; ring
    rw [hH, hH, e1]
    rw [← hGdef] at s1 s2
    have := max_le_iff.1 (le_refl (max (G (r1 - h * d / (h + p)))
      (G (r1 + Q₁ + p * d / (h + p)))))
    rcases le_total (G (r1 - h * d / (h + p))) (G (r1 + Q₁ + p * d / (h + p)))
      with hm | hm
    · rw [max_eq_right hm] at k; linarith
    · rw [max_eq_left hm] at k; linarith

  have lb : ∀ Q, 0 ≤ Q → h * p / (h + p) * Q ≤ Hfun (newsvendorCost h p μ) Q := by
    intro Q hQ
    obtain ⟨r, e1, e2⟩ := win Q hQ
    obtain ⟨l1, -⟩ := nv_lb hh hp hμ (r + Q)
    obtain ⟨-, l2⟩ := nv_lb hh hp hμ r
    rw [← hGdef, e2] at l1
    rw [← hGdef] at l2
    rw [hH, e1, div_mul_eq_mul_div, div_le_iff₀ hhp]
    nlinarith
  refine ⟨?_, chord, lb⟩
  · -- strict
    intro Q₁ hQ1 Q₂ hQ2 h12
    simp only [Set.mem_Ici] at hQ1 hQ2
    have hQ2p : 0 < Q₂ := by linarith
    obtain ⟨e1, e2⟩ := H_pos G hc hcv hy0 Q₂ hQ2p
    set r2 := optReorder G Q₂ with hr2
    have hlt : G y0 < G r2 := by
      rcases lt_or_ge (G y0) (G r2) with h | h
      · exact h
      · exfalso
        have m1 : ∀ z, G r2 ≤ G z := fun z => h.trans (hy0 z)
        have m2 : ∀ z, G (r2 + Q₂) ≤ G z := fun z => by rw [e2]; exact m1 z
        have := huniq _ m1
        have := huniq _ m2
        linarith
    have hy1 : r2 < y0 := by
      rcases le_or_gt y0 r2 with h | h
      · have := outside_left G hcv hQ2p e2 h; linarith
      · exact h
    have hy2 : y0 < r2 + Q₂ := by
      by_contra hcon
      have := outside_right G hcv hQ2p e2 (not_lt.1 hcon)
      linarith
    set d := (Q₂ - Q₁) / 2 with hd
    have hd0 : 0 < d := by rw [hd]; linarith
    have k := hle Q₁ hQ1 (r2 + d)
    have i1 := inside_lt G hcv e2 hlt hy1 hy2 (z := r2 + d) (by linarith)
      (by rw [hd]; linarith)
    have i2 := inside_lt G hcv e2 hlt hy1 hy2 (z := r2 + d + Q₁) (by linarith)
      (by rw [hd]; linarith)
    rw [hH, hH, e1]
    exact lt_of_le_of_lt k (max_lt i1 i2)


end EOQ

end P25e96b3b

open MeasureTheory Filter Topology ZhengQR.OrderQty in
theorem solution
    {lam L h p : ℝ} {μ : Measure ℝ}
    (hlam : 0 < lam) (hL : 0 < L) (hh : 0 < h) (hp : 0 < p)
    (hμ : IsLeadtimeDemand lam L μ)
    (hG : ∃! y : ℝ, IsMinimizer (newsvendorCost h p μ) y)
    {Q : ℝ} (hQ : 0 ≤ Q) :
    H0fun (newsvendorCost h p μ) Q ≤ Hfun (eoqCost lam L h p) Q ∧
    Hfun (eoqCost lam L h p) Q ≤ Hfun (newsvendorCost h p μ) Q ∧
    Afun (newsvendorCost h p μ) Q ≤ Afun (eoqCost lam L h p) Q := by
  obtain ⟨hsm, chord, lb⟩ := P25e96b3b.H_facts hh hp hμ hG
  have hHd := P25e96b3b.Hd_eq (lam := lam) (L := L) hh hp Q hQ
  set c := h * p / (h + p) with hc
  set G := newsvendorCost h p μ with hGdef
  set Gd := eoqCost lam L h p with hGd
  have hH0 : Hfun G 0 = G (minPoint G) := P25e96b3b.H_zero _
  have hH0Q : H0fun G Q = Hfun G Q - Hfun G 0 := by
    rw [hH0]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hH0Q, hHd]
    have := chord 0 Q le_rfl hQ
    linarith
  · rw [hHd]; exact lb Q hQ
  · have hA : Afun G Q = Q * Hfun G Q - ∫ y in (0:ℝ)..Q, Hfun G y := rfl
    have hAd : Afun Gd Q = Q * Hfun Gd Q - ∫ y in (0:ℝ)..Q, Hfun Gd y := rfl
    have i1 : (∫ y in (0:ℝ)..Q, Hfun Gd y) = ∫ y in (0:ℝ)..Q, c * y := by
      refine intervalIntegral.integral_congr (fun y hy => ?_)
      rw [Set.uIcc_of_le hQ] at hy
      exact P25e96b3b.Hd_eq hh hp y hy.1
    have i2 : (∫ y in (0:ℝ)..Q, c * y) = c * (Q ^ 2 / 2) := by
      rw [intervalIntegral.integral_const_mul, integral_id]; ring
    have hmono : MonotoneOn (Hfun G) (Set.uIcc 0 Q) :=
      hsm.monotoneOn.mono (by rw [Set.uIcc_of_le hQ]; exact Set.Icc_subset_Ici_self)
    have hint : IntervalIntegrable (Hfun G) MeasureTheory.volume 0 Q := hmono.intervalIntegrable
    have hlin : IntervalIntegrable (fun y => (Hfun G Q - c * Q) + c * y) MeasureTheory.volume 0 Q :=
      (by fun_prop : Continuous (fun y : ℝ => (Hfun G Q - c * Q) + c * y)).intervalIntegrable _ _
    have i3 : (∫ y in (0:ℝ)..Q, ((Hfun G Q - c * Q) + c * y)) ≤ ∫ y in (0:ℝ)..Q, Hfun G y := by
      refine intervalIntegral.integral_mono_on hQ hlin hint (fun y hy => ?_)
      have := chord y Q hy.1 hy.2
      linarith
    have i4 : (∫ y in (0:ℝ)..Q, ((Hfun G Q - c * Q) + c * y)) =
        Q * (Hfun G Q - c * Q) + c * (Q ^ 2 / 2) := by
      have hcy : IntervalIntegrable (fun y : ℝ => c * y) MeasureTheory.volume 0 Q :=
        (by fun_prop : Continuous (fun y : ℝ => c * y)).intervalIntegrable _ _
      rw [intervalIntegral.integral_add intervalIntegrable_const hcy,
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id,
        smul_eq_mul]
      ring
    rw [hA, hAd, i1, i2, hHd]
    rw [i4] at i3
    nlinarith

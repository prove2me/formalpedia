-- Prove2me | solution 1 for ZhengQR.CostBounds.area_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T15:24:17.292434+00:00
-- url     : https://prove2.me/submissions/48a220c5-3ffe-4517-b76a-6f9e8b809d4e

import Mathlib
import Definitions.Def_ZhengQR_CostBounds_QRMachinery
import Definitions.Def_ZhengQR_CostBounds_Model

set_option autoImplicit false

namespace Paa2fa7f6

open ZhengQR.CostBounds MeasureTheory

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

lemma opt_iff (G : ℝ → ℝ) (lam K Q r : ℝ) (hQ : 0 < Q) :
    IsOptReorder G lam K Q r ↔ ∀ r', (∫ y in r..r + Q, G y) ≤ ∫ y in r'..r' + Q, G y := by
  unfold IsOptReorder qrCost
  simp only [div_le_div_iff_of_pos_right hQ, add_le_add_iff_left]

lemma H_pos (G : ℝ → ℝ) (hc : Continuous G) (hcv : ConvexOn ℝ Set.univ G) {y0 : ℝ}
    (hy0 : ∀ z, G y0 ≤ G z) (lam K Q : ℝ) (hQ : 0 < Q) :
    Hfun G lam K Q = G (reorderPt G lam K Q) ∧
      G (reorderPt G lam K Q + Q) = G (reorderPt G lam K Q) := by
  obtain ⟨r0, hr0⟩ := exists_min G hc hcv hy0 hQ.le
  have hex : ∃ r, IsOptReorder G lam K Q r := ⟨r0, (opt_iff G lam K Q r0 hQ).2 hr0⟩
  have hspec : IsOptReorder G lam K Q (reorderPt G lam K Q) := by
    unfold reorderPt; rw [dif_pos hex]; exact hex.choose_spec
  refine ⟨?_, balance_of_min G hc ((opt_iff G lam K Q _ hQ).1 hspec)⟩
  unfold Hfun; rw [if_pos hQ]

lemma idealPt_spec (G : ℝ → ℝ) {y0 : ℝ} (hy0 : ∀ z, G y0 ≤ G z) :
    ∀ z, G (idealPt G) ≤ G z := by
  have hex : ∃ y, ∀ z, G y ≤ G z := ⟨y0, hy0⟩
  unfold idealPt; rw [dif_pos hex]; exact hex.choose_spec

lemma H_zero (G : ℝ → ℝ) (lam K : ℝ) : Hfun G lam K 0 = G (idealPt G) := by
  unfold Hfun; rw [if_neg (lt_irrefl 0)]

lemma Hwin (G : ℝ → ℝ) (hc : Continuous G) (hcv : ConvexOn ℝ Set.univ G) {y0 : ℝ}
    (hy0 : ∀ z, G y0 ≤ G z) (lam K Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ r, Hfun G lam K Q = G r ∧ G (r + Q) = G r := by
  rcases eq_or_lt_of_le hQ with h | h
  · subst h
    exact ⟨idealPt G, H_zero G lam K, by rw [add_zero]⟩
  · exact ⟨_, H_pos G hc hcv hy0 lam K Q h⟩

lemma Hle (G : ℝ → ℝ) (hc : Continuous G) (hcv : ConvexOn ℝ Set.univ G) {y0 : ℝ}
    (hy0 : ∀ z, G y0 ≤ G z) (lam K Q : ℝ) (hQ : 0 ≤ Q) (r : ℝ) :
    Hfun G lam K Q ≤ max (G r) (G (r + Q)) := by
  rcases eq_or_lt_of_le hQ with h | h
  · subst h
    rw [H_zero]
    exact (idealPt_spec G hy0 r).trans (le_max_left _ _)
  · obtain ⟨e1, e2⟩ := H_pos G hc hcv hy0 lam K Q h
    rw [e1]
    exact ge_of_win G hcv h e2 r

/-! ## The newsvendor cost -/

section NV

variable (M : QRModel)

lemma integ (y : ℝ) :
    Integrable (fun x => M.h * max (y - x) 0 + M.p * max (x - y) 0) M.μ := by
  have := M.isProb
  have hg : Integrable (fun x => (M.h + M.p) * (|y| + |x|)) M.μ :=
    ((integrable_const |y|).add M.integrable_id.abs).const_mul (M.h + M.p)
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
    newsvendorCost M.μ M.h M.p y2 - newsvendorCost M.μ M.h M.p y1 ≤ M.h * (y2 - y1) := by
  have := M.isProb
  have hh := M.h_pos
  have hp := M.p_pos
  have key : newsvendorCost M.μ M.h M.p y2 ≤
      ∫ x, ((M.h * max (y1 - x) 0 + M.p * max (x - y1) 0) + M.h * (y2 - y1)) ∂M.μ := by
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
    newsvendorCost M.μ M.h M.p y1 - newsvendorCost M.μ M.h M.p y2 ≤ M.p * (y2 - y1) := by
  have := M.isProb
  have hh := M.h_pos
  have hp := M.p_pos
  have key : newsvendorCost M.μ M.h M.p y1 ≤
      ∫ x, ((M.h * max (y2 - x) 0 + M.p * max (x - y2) 0) + M.p * (y2 - y1)) ∂M.μ := by
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

lemma nv_convex : ConvexOn ℝ Set.univ (newsvendorCost M.μ M.h M.p) := by
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

lemma nv_cont : Continuous (newsvendorCost M.μ M.h M.p) := by
  have hh := M.h_pos
  have hp := M.p_pos
  refine (LipschitzWith.of_le_add_mul' (M.h + M.p) (fun x y => ?_)).continuous
  rw [Real.dist_eq]
  rcases le_total y x with h | h
  · have := nv_slope_r M h
    have : M.h * (x - y) ≤ (M.h + M.p) * |x - y| := by
      rw [abs_of_nonneg (by linarith)]; nlinarith
    linarith
  · have := nv_slope_l M h
    have : M.p * (y - x) ≤ (M.h + M.p) * |x - y| := by
      rw [abs_of_nonpos (by linarith)]; nlinarith
    linarith

lemma nv_lb (y : ℝ) :
    M.h * (y - M.lam * M.L) ≤ newsvendorCost M.μ M.h M.p y ∧
      M.p * (M.lam * M.L - y) ≤ newsvendorCost M.μ M.h M.p y := by
  have := M.isProb
  have hh := M.h_pos
  have hp := M.p_pos
  have i1 : Integrable (fun x => M.h * y - M.h * x) M.μ :=
    (integrable_const _).sub (M.integrable_id.const_mul _)
  have i2 : Integrable (fun x => M.p * x - M.p * y) M.μ :=
    (M.integrable_id.const_mul _).sub (integrable_const _)
  have e1 : ∫ x, (M.h * y - M.h * x) ∂M.μ = M.h * (y - M.lam * M.L) := by
    rw [integral_sub (integrable_const _) (M.integrable_id.const_mul _), integral_const,
      probReal_univ, one_smul, integral_const_mul, M.mean_eq]
    ring
  have e2 : ∫ x, (M.p * x - M.p * y) ∂M.μ = M.p * (M.lam * M.L - y) := by
    rw [integral_sub (M.integrable_id.const_mul _) (integrable_const _), integral_const,
      probReal_univ, one_smul, integral_const_mul, M.mean_eq]
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


lemma rp_indep (G : ℝ → ℝ) (lam K K' Q : ℝ) (hQ : 0 < Q) :
    reorderPt G lam K Q = reorderPt G lam K' Q := by
  have e : IsOptReorder G lam K Q = IsOptReorder G lam K' Q :=
    funext fun r => propext ((opt_iff G lam K Q r hQ).trans (opt_iff G lam K' Q r hQ).symm)
  unfold reorderPt
  rw [e]

lemma H_indep (G : ℝ → ℝ) (lam K K' : ℝ) : Hfun G lam K = Hfun G lam K' := by
  funext Q
  unfold Hfun
  by_cases hQ : 0 < Q
  · rw [if_pos hQ, if_pos hQ, rp_indep G lam K K' Q hQ]
  · rw [if_neg hQ, if_neg hQ]

lemma A_indep (G : ℝ → ℝ) (lam K K' : ℝ) : Afun G lam K = Afun G lam K' := by
  funext Q
  unfold Afun
  rw [H_indep G lam K K']

lemma idealPt_eq (G : ℝ → ℝ) {y0 : ℝ} (hy0 : ∀ z, G y0 ≤ G z)
    (hu : ∀ y, (∀ z, G y ≤ G z) → y = y0) : idealPt G = y0 := by
  have hex : ∃ y, ∀ z, G y ≤ G z := ⟨y0, hy0⟩
  apply hu
  unfold idealPt; rw [dif_pos hex]; exact hex.choose_spec

lemma chord (M : QRModel) (K : ℝ) : ∀ Q₁ Q₂ : ℝ, 0 ≤ Q₁ → Q₁ ≤ Q₂ →
    Hfun M.G M.lam K Q₂ - Hfun M.G M.lam K Q₁ ≤ M.h * M.p / (M.h + M.p) * (Q₂ - Q₁) := by
  have hMG : M.G = newsvendorCost M.μ M.h M.p := rfl
  rw [hMG]
  set G := newsvendorCost M.μ M.h M.p with hGdef
  have hc : Continuous G := nv_cont M
  have hcv : ConvexOn ℝ Set.univ G := nv_convex M
  obtain ⟨y0, hy0, -⟩ := M.unique_min
  have hh := M.h_pos
  have hp := M.p_pos
  have win := Hwin G hc hcv hy0 M.lam K
  have hle := Hle G hc hcv hy0 M.lam K
  intro Q₁ Q₂ hQ1 hQ12
  obtain ⟨r1, e1, e2⟩ := win Q₁ hQ1
  set d := Q₂ - Q₁ with hd
  have hd0 : 0 ≤ d := by linarith
  have k := hle Q₂ (by linarith) (r1 - M.h * d / (M.h + M.p))
  have hpt : r1 - M.h * d / (M.h + M.p) + Q₂ = (r1 + Q₁) + M.p * d / (M.h + M.p) := by
    field_simp; rw [hd]; ring
  rw [hpt] at k
  have s1 := nv_slope_l M
    (show r1 - M.h * d / (M.h + M.p) ≤ r1 by
      have : 0 ≤ M.h * d / (M.h + M.p) := by positivity
      linarith)
  have s2 := nv_slope_r M
    (show r1 + Q₁ ≤ (r1 + Q₁) + M.p * d / (M.h + M.p) by
      have : 0 ≤ M.p * d / (M.h + M.p) := by positivity
      linarith)
  have c1 : M.p * (r1 - (r1 - M.h * d / (M.h + M.p))) = M.h * M.p / (M.h + M.p) * d := by
    field_simp; ring
  have c2 : M.h * ((r1 + Q₁) + M.p * d / (M.h + M.p) - (r1 + Q₁)) =
      M.h * M.p / (M.h + M.p) * d := by
    field_simp; ring
  rw [e1]
  rw [← hGdef] at s1 s2
  rcases le_total (G (r1 - M.h * d / (M.h + M.p))) (G (r1 + Q₁ + M.p * d / (M.h + M.p)))
    with hm | hm
  · rw [max_eq_right hm] at k; linarith
  · rw [max_eq_left hm] at k; linarith

lemma lb (M : QRModel) (K : ℝ) : ∀ Q, 0 ≤ Q →
    M.h * M.p / (M.h + M.p) * Q ≤ Hfun M.G M.lam K Q := by
  have hMG : M.G = newsvendorCost M.μ M.h M.p := rfl
  rw [hMG]
  set G := newsvendorCost M.μ M.h M.p with hGdef
  have hc : Continuous G := nv_cont M
  have hcv : ConvexOn ℝ Set.univ G := nv_convex M
  obtain ⟨y0, hy0, -⟩ := M.unique_min
  have hh := M.h_pos
  have hp := M.p_pos
  have hhp : 0 < M.h + M.p := add_pos hh hp
  have win := Hwin G hc hcv hy0 M.lam K
  intro Q hQ
  obtain ⟨r, e1, e2⟩ := win Q hQ
  obtain ⟨l1, -⟩ := nv_lb M (r + Q)
  obtain ⟨-, l2⟩ := nv_lb M r
  rw [← hGdef, e2] at l1
  rw [← hGdef] at l2
  rw [e1, div_mul_eq_mul_div, div_le_iff₀ hhp]
  nlinarith

lemma H_convex (M : QRModel) (K : ℝ) : ConvexOn ℝ (Set.Ici 0) (Hfun M.G M.lam K) := by
  have hMG : M.G = newsvendorCost M.μ M.h M.p := rfl
  rw [hMG]
  set G := newsvendorCost M.μ M.h M.p with hGdef
  have hc : Continuous G := nv_cont M
  have hcv : ConvexOn ℝ Set.univ G := nv_convex M
  obtain ⟨y0, hy0, -⟩ := M.unique_min
  have win := Hwin G hc hcv hy0 M.lam K
  have hle := Hle G hc hcv hy0 M.lam K
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [Set.mem_Ici] at hx hy
  obtain ⟨rx, ex1, ex2⟩ := win x hx
  obtain ⟨ry, ey1, ey2⟩ := win y hy
  have hxy : 0 ≤ a • x + b • y := by
    simp only [smul_eq_mul]; positivity
  have k := hle _ hxy (a * rx + b * ry)
  have c1 := hcv.2 (Set.mem_univ rx) (Set.mem_univ ry) ha hb hab
  have c2 := hcv.2 (Set.mem_univ (rx + x)) (Set.mem_univ (ry + y)) ha hb hab
  simp only [smul_eq_mul] at c1 c2 k ⊢
  have hpt : a * rx + b * ry + (a * x + b * y) = a * (rx + x) + b * (ry + y) := by ring
  rw [hpt] at k
  rw [ex1, ey1]
  rw [ex2, ey2] at c2
  exact k.trans (max_le c1 c2)

lemma env (M : QRModel) (K : ℝ) :
    MonotoneOn (Hfun M.G M.lam K) (Set.Ici 0) ∧
    StrictMonoOn (Hfun M.G M.lam K) (Set.Ici 0) ∧
    (∀ a b : ℝ, 0 < a → a < b → reorderPt M.G M.lam K b < reorderPt M.G M.lam K a) ∧
    (∀ a b : ℝ, 0 ≤ a → a ≤ b →
      (b - a) * Hfun M.G M.lam K a ≤
          (∫ y in (0:ℝ)..b, Hfun M.G M.lam K y) - (∫ y in (0:ℝ)..a, Hfun M.G M.lam K y) ∧
        (∫ y in (0:ℝ)..b, Hfun M.G M.lam K y) - (∫ y in (0:ℝ)..a, Hfun M.G M.lam K y) ≤
          (b - a) * Hfun M.G M.lam K b) ∧
    (∀ Q : ℝ, 0 < Q → Q * Cfun M.G M.lam K Q = M.lam * K + ∫ y in (0:ℝ)..Q, Hfun M.G M.lam K y) := by
  have hMG : M.G = newsvendorCost M.μ M.h M.p := rfl
  rw [hMG]
  set G := newsvendorCost M.μ M.h M.p with hGdef
  set lam := M.lam
  have hc : Continuous G := nv_cont M
  have hcv : ConvexOn ℝ Set.univ G := nv_convex M
  obtain ⟨y0, hy0, huniq⟩ := M.unique_min
  have hu : ∀ y, (∀ z, G y ≤ G z) → y = y0 := huniq
  have hmin : idealPt G = y0 := idealPt_eq G hy0 hu
  have hstr : ∀ a, a ≠ y0 → G y0 < G a := by
    intro a ha
    rcases lt_or_ge (G y0) (G a) with h1 | h1
    · exact h1
    · exact absurd (hu a fun z => h1.trans (hy0 z)) ha
  set r := reorderPt G lam K with hr
  have bal : ∀ q, 0 < q → G (r q + q) = G (r q) := fun q hq =>
    (H_pos G hc hcv hy0 lam K q hq).2
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
      have := outside_left G hcv hq e (not_lt.1 hcon)
      linarith
    · by_contra hcon
      have := outside_right G hcv hq e (not_lt.1 hcon)
      linarith
  have nest : ∀ a b, 0 < a → a < b → r b < r a ∧ r a + a < r b + b := by
    intro a b ha hab
    have hb : 0 < b := ha.trans hab
    obtain ⟨a1, a2⟩ := pos a ha
    obtain ⟨b1, b2⟩ := pos b hb
    constructor
    · by_contra hcon
      have hle : r a ≤ r b := not_lt.1 hcon
      have g1 : G (r b) ≤ G (r a) := by
        rcases eq_or_lt_of_le hle with h1 | h1
        · rw [h1]
        · exact (strict_left G hcv (hstr _ (ne_of_lt a1)) h1 b1.le).le
      have g2 : G (r a + a) < G (r b + b) :=
        strict_right G hcv (hstr _ (ne_of_gt (by linarith))) a2.le (by linarith)
      have e := bal a ha
      have e' := bal b hb
      linarith
    · by_contra hcon
      have hle : r b + b ≤ r a + a := not_lt.1 hcon
      have g1 : G (r a) < G (r b) :=
        strict_left G hcv (hstr _ (ne_of_lt (by linarith))) (by linarith) a1.le
      have g2 : G (r b + b) ≤ G (r a + a) := by
        rcases eq_or_lt_of_le hle with h1 | h1
        · rw [h1]
        · exact (strict_right G hcv (hstr _ (ne_of_gt a2)) b2.le h1).le
      have e := bal a ha
      have e' := bal b hb
      linarith
  set H := Hfun G lam K with hHdef
  have Hpos : ∀ q, 0 < q → H q = G (r q) := fun q hq => by
    show Hfun G lam K q = G (reorderPt G lam K q)
    rw [Hfun, if_pos hq]
  have H0 : H 0 = G y0 := by simp only [hHdef, Hfun, lt_irrefl, if_false, hmin]
  have Hstrict : StrictMonoOn H (Set.Ici 0) := by
    intro a ha b hb hab
    simp only [Set.mem_Ici] at ha hb
    have hb0 : 0 < b := lt_of_le_of_lt ha hab
    obtain ⟨b1, -⟩ := pos b hb0
    have gb : G y0 < G (r b) := hstr _ (ne_of_lt b1)
    rw [Hpos b hb0]
    rcases eq_or_lt_of_le ha with h0 | h0
    · subst h0
      rw [H0]; exact gb
    · rw [Hpos a h0]
      obtain ⟨n1, -⟩ := nest a b h0 hab
      obtain ⟨a1, -⟩ := pos a h0
      exact strict_left G hcv gb n1 a1.le
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
      have := int_bounds G hc (α := r b) (β := r b + b) (lo := G y0) (hi := G (r b))
        (by linarith) (fun z _ => hy0 z)
        (fun z hz => inside_le G hcv hb (bal b hb) hz.1 hz.2)
      simp only [add_sub_cancel_left] at this
      exact this
    · rw [Hpos a h0]
      obtain ⟨n1, n2⟩ := nest a b h0 hab
      exact W_step G hc hcv h0 hab (bal a h0) (bal b hb) n1 n2
  have Hmono : MonotoneOn H (Set.Ici 0) := Hstrict.monotoneOn
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
  refine ⟨Hmono, Hstrict, fun a b ha hab => (nest a b ha hab).1, Ib, fun Q hQ => ?_⟩
  have key : (W Q - I Q) - (W 0 - I 0) = 0 :=
    eq_of_tele (Q := Q) (c := H Q - H 0) fun n hn =>
      tele (fun q => W q - I q) H hQ.le hE n hn
  rw [W0, I0] at key
  have conj0 : W Q = I Q := by linarith
  have conj1 : (∫ y in r Q..r Q + Q, G y) = ∫ y in (0 : ℝ)..Q, H y := conj0
  have ec : Cfun G lam K Q = (lam * K + ∫ y in r Q..r Q + Q, G y) / Q := rfl
  rw [ec, conj1]
  field_simp

lemma H_cont (M : QRModel) (K : ℝ) : Continuous (Hfun M.G M.lam K) := by
  have hmono := (env M K).1
  have hch := chord M K
  have hh := M.h_pos
  have hp := M.p_pos
  set c := M.h * M.p / (M.h + M.p) with hc
  have cpos : 0 < c := by positivity
  have hneg : ∀ x, Hfun M.G M.lam K x = Hfun M.G M.lam K (max x 0) := by
    intro x
    rcases le_total x 0 with h | h
    · rw [max_eq_right h]
      unfold Hfun
      rw [if_neg (not_lt.2 h), if_neg (lt_irrefl 0)]
    · rw [max_eq_left h]
  refine (LipschitzWith.of_le_add_mul' c (fun x y => ?_)).continuous
  rw [hneg x, hneg y, Real.dist_eq]
  have hd := abs_max_sub_max_le_abs x y 0
  have hx0 : (0:ℝ) ≤ max x 0 := le_max_right _ _
  have hy0 : (0:ℝ) ≤ max y 0 := le_max_right _ _
  rcases le_total (max x 0) (max y 0) with h | h
  · have := hmono hx0 hy0 h
    have : 0 ≤ c * |x - y| := by positivity
    linarith
  · have k := hch _ _ hy0 h
    have : max x 0 - max y 0 ≤ |x - y| := (le_abs_self _).trans hd
    have : c * (max x 0 - max y 0) ≤ c * |x - y| := mul_le_mul_of_nonneg_left this cpos.le
    linarith

/-- optimality at an arbitrary fixed cost `K > 0` -/
lemma optK (M : QRModel) (K : ℝ) (hK : 0 < K) :
    (∃ Q : ℝ, IsOptQty M.G M.lam K Q) ∧
      ∀ Q : ℝ, 0 < Q → (IsOptQty M.G M.lam K Q ↔ Afun M.G M.lam K Q = M.lam * K) := by
  obtain ⟨Hmono, -, -, Ib, cost⟩ := env M K
  have chord := chord M K
  have lbd := lb M K
  have hHc := H_cont M K
  have hh := M.h_pos
  have hp := M.p_pos
  have hlK : 0 < M.lam * K := mul_pos M.lam_pos hK
  set c := M.h * M.p / (M.h + M.p) with hc
  have cpos : 0 < c := by positivity
  set H := Hfun M.G M.lam K with hHdef
  set C := Cfun M.G M.lam K with hCdef
  set I : ℝ → ℝ := fun q => ∫ y in (0 : ℝ)..q, H y with hI
  have I0 : I 0 = 0 := by simp only [hI, intervalIntegral.integral_same]
  have O3 : ∀ Q : ℝ, 0 < Q → H Q = C Q → IsOptQty M.G M.lam K Q := by
    intro Q hQ hHC
    refine ⟨hQ, fun Q' hQ' => ?_⟩
    have e1 := cost Q hQ
    have e2 := cost Q' hQ'
    have key : Q' * H Q ≤ Q' * C Q' := by
      rcases le_total Q Q' with h | h
      · obtain ⟨i1, -⟩ := Ib Q Q' hQ.le h
        rw [← hHC] at e1
        nlinarith
      · obtain ⟨-, i2⟩ := Ib Q' Q hQ'.le h
        rw [← hHC] at e1
        nlinarith
    show C Q ≤ C Q'
    rw [← hHC]
    exact le_of_mul_le_mul_left key hQ'
  have O2 : ∀ Q : ℝ, IsOptQty M.G M.lam K Q → H Q = C Q := by
    rintro Q ⟨hQ, hopt⟩
    have up : ∀ δ : ℝ, 0 < δ → C Q ≤ H Q + c * δ := by
      intro δ hδ
      have e1 := cost Q hQ
      have e2 := cost (Q + δ) (by linarith)
      obtain ⟨-, i2⟩ := Ib Q (Q + δ) hQ.le (by linarith)
      have ch := chord Q (Q + δ) hQ.le (by linarith)
      have ho : C Q ≤ C (Q + δ) := hopt (Q + δ) (by linarith)
      have m1 := mul_le_mul_of_nonneg_left ho (by linarith : (0:ℝ) ≤ Q + δ)
      have m2 := mul_le_mul_of_nonneg_left ch hδ.le
      have k : δ * C Q ≤ δ * (H Q + c * δ) := by
        simp only [add_sub_cancel_left] at i2 m2
        nlinarith
      exact le_of_mul_le_mul_left k hδ
    have down : ∀ δ : ℝ, 0 < δ → δ < Q → H Q ≤ C Q + c * δ := by
      intro δ hδ hδQ
      have e1 := cost Q hQ
      have e2 := cost (Q - δ) (by linarith)
      obtain ⟨i1, -⟩ := Ib (Q - δ) Q (by linarith) (by linarith)
      have ch := chord (Q - δ) Q (by linarith) (by linarith)
      have ho : C Q ≤ C (Q - δ) := hopt (Q - δ) (by linarith)
      have m1 := mul_le_mul_of_nonneg_left ho (by linarith : (0:ℝ) ≤ Q - δ)
      have m2 := mul_le_mul_of_nonneg_left ch hδ.le
      have k : δ * H Q ≤ δ * (C Q + c * δ) := by
        simp only [sub_sub_cancel] at i1 m2
        nlinarith
      exact le_of_mul_le_mul_left k hδ
    apply le_antisymm
    · apply le_of_forall_pos_le_add
      intro ε hε
      set δ := min (Q / 2) (ε / c) with hδ
      have hδ0 : 0 < δ := lt_min (by linarith) (div_pos hε cpos)
      have hδQ : δ < Q := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hcδ : c * δ ≤ ε := by
        have : δ ≤ ε / c := min_le_right _ _
        rw [le_div_iff₀ cpos] at this
        linarith
      linarith [down δ hδ0 hδQ]
    · apply le_of_forall_pos_le_add
      intro ε hε
      have := up (ε / c) (div_pos hε cpos)
      have e : c * (ε / c) = ε := by field_simp
      linarith
  have HC_iff : ∀ Q : ℝ, 0 < Q → (H Q = C Q ↔ Afun M.G M.lam K Q = M.lam * K) := by
    intro Q hQ
    have e := cost Q hQ
    have eA : Afun M.G M.lam K Q = Q * H Q - I Q := rfl
    rw [eA]
    constructor
    · intro h
      rw [h, e]
      simp only [hI]
      ring
    · intro h
      have k : Q * H Q = Q * C Q := by
        rw [e]; simp only [hI] at h; linarith
      exact mul_left_cancel₀ hQ.ne' k
  refine ⟨?_, fun Q hQ => ⟨fun h => (HC_iff Q hQ).1 (O2 Q h),
    fun h => O3 Q hQ ((HC_iff Q hQ).2 h)⟩⟩
  have hIc : Continuous I := continuous_iff_continuousAt.2 fun q =>
    (hHc.integral_hasStrictDerivAt 0 q).hasDerivAt.continuousAt
  set Φ : ℝ → ℝ := fun q => q * H q - I q with hΦ
  have hΦc : Continuous Φ := (continuous_id.mul hHc).sub hIc
  have Φ0 : Φ 0 = 0 := by simp only [hΦ, I0, zero_mul, sub_zero]
  set Qb := (M.lam * K + |H 1|) / c + 1 with hQb
  have hQb1 : 1 ≤ Qb := by
    have : 0 ≤ (M.lam * K + |H 1|) / c := by positivity
    linarith
  have ΦQb : M.lam * K ≤ Φ Qb := by
    obtain ⟨-, i2⟩ := Ib 1 Qb zero_le_one hQb1
    obtain ⟨-, i3⟩ := Ib 0 1 le_rfl zero_le_one
    have l := lbd Qb (by linarith)
    have e : c * Qb = M.lam * K + |H 1| + c := by
      rw [hQb]; field_simp
    have a1 := le_abs_self (H 1)
    show M.lam * K ≤ Qb * H Qb - ∫ y in (0:ℝ)..Qb, H y
    rw [intervalIntegral.integral_same] at i3
    nlinarith
  obtain ⟨Qs, ⟨hQs0, -⟩, hQs⟩ := intermediate_value_Icc (le_trans zero_le_one hQb1)
    hΦc.continuousOn ⟨by rw [Φ0]; exact hlK.le, ΦQb⟩
  have hQsp : 0 < Qs := by
    rcases eq_or_lt_of_le hQs0 with h | h
    · rw [← h, Φ0] at hQs; linarith
    · exact h
  exact ⟨Qs, O3 Qs hQsp ((HC_iff Qs hQsp).2 hQs)⟩

/-- `A` strictly increasing and convex on `[0, ∞)` -/
lemma A_props (M : QRModel) (K : ℝ) :
    StrictMonoOn (Afun M.G M.lam K) (Set.Ici 0) ∧ ConvexOn ℝ (Set.Ici 0) (Afun M.G M.lam K) := by
  obtain ⟨Hmono, Hstrict, -, Ib, -⟩ := env M K
  have Hcv := H_convex M K
  set H := Hfun M.G M.lam K with hHdef
  set I : ℝ → ℝ := fun q => ∫ y in (0 : ℝ)..q, H y with hI
  have eA : ∀ Q, Afun M.G M.lam K Q = Q * H Q - I Q := fun Q => rfl
  -- A b - A a ≤ b (H b - H a) and ≥ a (H b - H a)
  have up : ∀ a b, 0 ≤ a → a ≤ b → Afun M.G M.lam K b - Afun M.G M.lam K a ≤ b * (H b - H a) := by
    intro a b ha hab
    obtain ⟨i1, -⟩ := Ib a b ha hab
    rw [eA, eA]
    simp only [hI] at i1 ⊢
    nlinarith
  have dn : ∀ a b, 0 ≤ a → a ≤ b → a * (H b - H a) ≤ Afun M.G M.lam K b - Afun M.G M.lam K a := by
    intro a b ha hab
    obtain ⟨-, i2⟩ := Ib a b ha hab
    rw [eA, eA]
    simp only [hI] at i2 ⊢
    nlinarith
  constructor
  · intro a ha b hb hab
    simp only [Set.mem_Ici] at ha hb
    set m := (a + b) / 2 with hm
    have hm0 : 0 ≤ m := by rw [hm]; linarith
    have ham : a ≤ m := by rw [hm]; linarith
    have hmb : m < b := by rw [hm]; linarith
    have k1 := dn a m ha ham
    have k2 := dn m b hm0 hmb.le
    have s1 : H m < H b := Hstrict hm0 hb hmb
    have s2 : H a ≤ H m := Hmono ha hm0 ham
    have k3 : 0 < m * (H b - H m) := by
      have : 0 < m := by rw [hm]; linarith
      exact mul_pos this (by linarith)
    have k4 : 0 ≤ a * (H m - H a) := mul_nonneg ha (by linarith)
    linarith
  · refine convexOn_of_slope_mono_adjacent (convex_Ici 0) ?_
    intro x y z hx hz hxy hyz
    simp only [Set.mem_Ici] at hx hz
    have hy : 0 ≤ y := by linarith
    have u := up x y hx hxy.le
    have d := dn y z hy hyz.le
    have hs := Hcv.slope_mono_adjacent (Set.mem_Ici.2 hx) (Set.mem_Ici.2 hz) hxy hyz
    have p1 : 0 < y - x := by linarith
    have p2 : 0 < z - y := by linarith
    calc (Afun M.G M.lam K y - Afun M.G M.lam K x) / (y - x)
        ≤ y * ((H y - H x) / (y - x)) := by
          rw [mul_div_assoc', div_le_div_iff_of_pos_right p1]; exact u
      _ ≤ y * ((H z - H y) / (z - y)) := mul_le_mul_of_nonneg_left hs hy
      _ ≤ (Afun M.G M.lam K z - Afun M.G M.lam K y) / (z - y) := by
          rw [mul_div_assoc', div_le_div_iff_of_pos_right p2]; exact d

end Paa2fa7f6

open ZhengQR.CostBounds in
theorem solution (M : QRModel) :
    StrictMonoOn (Afun M.G M.lam M.K) (Set.Ici 0) ∧
    ConvexOn ℝ (Set.Ici 0) (Afun M.G M.lam M.K) ∧
    (∀ K' : ℝ, 0 < K' → ∃! Q : ℝ, IsOptQty M.G M.lam K' Q) ∧
    (∀ Q : ℝ, 0 < Q → (IsOptQty M.G M.lam M.K Q ↔ Afun M.G M.lam M.K Q = M.lam * M.K)) ∧
    (∀ K₁ K₂ Q₁ Q₂ : ℝ, 0 < K₁ → K₁ < K₂ →
      IsOptQty M.G M.lam K₁ Q₁ → IsOptQty M.G M.lam K₂ Q₂ →
      Q₁ < Q₂ ∧ reorderPt M.G M.lam K₂ Q₂ < reorderPt M.G M.lam K₁ Q₁) := by
  obtain ⟨hA1, hA2⟩ := Paa2fa7f6.A_props M M.K
  have Aind : ∀ K', Afun M.G M.lam K' = Afun M.G M.lam M.K := fun K' =>
    Paa2fa7f6.A_indep M.G M.lam K' M.K
  refine ⟨hA1, hA2, ?_, (Paa2fa7f6.optK M M.K M.K_pos).2, ?_⟩
  · intro K' hK'
    obtain ⟨⟨Q, hQ⟩, hiff⟩ := Paa2fa7f6.optK M K' hK'
    refine ⟨Q, hQ, fun Q' hQ' => ?_⟩
    have e1 := (hiff Q hQ.1).1 hQ
    have e2 := (hiff Q' hQ'.1).1 hQ'
    rw [Aind] at e1 e2
    exact hA1.injOn (Set.mem_Ici.2 hQ'.1.le) (Set.mem_Ici.2 hQ.1.le) (e2.trans e1.symm)
  · intro K₁ K₂ Q₁ Q₂ hK1 hK12 h1 h2
    have hK2 : 0 < K₂ := hK1.trans hK12
    have e1 := ((Paa2fa7f6.optK M K₁ hK1).2 Q₁ h1.1).1 h1
    have e2 := ((Paa2fa7f6.optK M K₂ hK2).2 Q₂ h2.1).1 h2
    rw [Aind] at e1 e2
    have hlt : Afun M.G M.lam M.K Q₁ < Afun M.G M.lam M.K Q₂ := by
      rw [e1, e2]; exact mul_lt_mul_of_pos_left hK12 M.lam_pos
    have hQ : Q₁ < Q₂ :=
      (hA1.lt_iff_lt (Set.mem_Ici.2 h1.1.le) (Set.mem_Ici.2 h2.1.le)).1 hlt
    refine ⟨hQ, ?_⟩
    rw [Paa2fa7f6.rp_indep M.G M.lam K₂ M.K Q₂ h2.1, Paa2fa7f6.rp_indep M.G M.lam K₁ M.K Q₁ h1.1]
    exact (Paa2fa7f6.env M M.K).2.2.1 Q₁ Q₂ h1.1 hQ

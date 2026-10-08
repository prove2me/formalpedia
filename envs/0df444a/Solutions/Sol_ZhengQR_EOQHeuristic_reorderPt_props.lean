-- Prove2me | solution 1 for ZhengQR.EOQHeuristic.reorderPt_props
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T11:18:32.875886+00:00
-- url     : https://prove2.me/submissions/3b063642-bbb7-46d8-92eb-69913c1c02f7

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel

set_option autoImplicit false

namespace P247a58c8

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


end P247a58c8

open ZhengQR.EOQHeuristic MeasureTheory Filter Topology in
theorem solution {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) :
    (∀ Q : ℝ, 0 < Q → ∀ K' : ℝ, 0 < K' →
        reorderPt (newsvendorCost μ h p) lam K Q = reorderPt (newsvendorCost μ h p) lam K' Q) ∧
    (∀ Q : ℝ, 0 < Q →
        reorderPt (newsvendorCost μ h p) lam K Q < minPt (newsvendorCost μ h p) ∧ minPt (newsvendorCost μ h p) < reorderPt (newsvendorCost μ h p) lam K Q + Q) ∧
    (∀ Q Q' : ℝ, 0 < Q → Q < Q' →
        reorderPt (newsvendorCost μ h p) lam K Q' < reorderPt (newsvendorCost μ h p) lam K Q ∧ reorderPt (newsvendorCost μ h p) lam K Q + Q < reorderPt (newsvendorCost μ h p) lam K Q' + Q') ∧
    Tendsto (reorderPt (newsvendorCost μ h p) lam K) atTop atBot ∧
    Tendsto (fun Q : ℝ => reorderPt (newsvendorCost μ h p) lam K Q + Q) atTop atTop := by
  set G := newsvendorCost μ h p with hGdef
  have hc : Continuous G := P247a58c8.nv_cont hM
  have hcv : ConvexOn ℝ Set.univ G := P247a58c8.nv_convex hM
  obtain ⟨y0, hy0, huniq⟩ := hM.unique_min
  have hu : ∀ y, (∀ z, G y ≤ G z) → y = y0 := huniq
  have hmin : minPt G = y0 := P247a58c8.minPt_eq G hy0 hu
  have hh := hM.h_pos
  have hp := hM.p_pos
  have hhp : 0 < h + p := add_pos hh hp
  have hstr : ∀ a, a ≠ y0 → G y0 < G a := by
    intro a ha
    rcases lt_or_ge (G y0) (G a) with h1 | h1
    · exact h1
    · exact absurd (hu a fun z => h1.trans (hy0 z)) ha
  set r := reorderPt G lam K with hr
  have bal : ∀ Q, 0 < Q → G (r Q + Q) = G (r Q) := fun Q hQ =>
    P247a58c8.rp_spec G hc hcv hy0 lam K Q hQ
  have pos : ∀ Q, 0 < Q → r Q < y0 ∧ y0 < r Q + Q := by
    intro Q hQ
    have e := bal Q hQ
    have hlt : G y0 < G (r Q) := by
      rcases eq_or_ne (r Q) y0 with h1 | h1
      · have h2 : r Q + Q ≠ y0 := by rw [h1]; linarith
        have := hstr _ h2
        rw [e] at this; exact this
      · exact hstr _ h1
    constructor
    · by_contra hcon
      have := P247a58c8.outside_left G hcv hQ e (not_lt.1 hcon)
      linarith
    · by_contra hcon
      have := P247a58c8.outside_right G hcv hQ e (not_lt.1 hcon)
      linarith
  refine ⟨fun Q hQ K' _ => P247a58c8.rp_indep G lam K K' Q hQ, ?_, ?_, ?_, ?_⟩
  · intro Q hQ
    rw [hmin]
    exact pos Q hQ
  · intro Q Q' hQ hQQ
    have hQ' : 0 < Q' := hQ.trans hQQ
    obtain ⟨a1, a2⟩ := pos Q hQ
    obtain ⟨b1, b2⟩ := pos Q' hQ'
    have e := bal Q hQ
    have e' := bal Q' hQ'
    constructor
    · by_contra hcon
      have hle : r Q ≤ r Q' := not_lt.1 hcon
      have g1 : G (r Q') ≤ G (r Q) := by
        rcases eq_or_lt_of_le hle with h1 | h1
        · rw [h1]
        · exact (P247a58c8.strict_left G hcv (hstr _ (ne_of_lt a1)) h1 b1.le).le
      have g2 : G (r Q + Q) < G (r Q' + Q') :=
        P247a58c8.strict_right G hcv (hstr _ (ne_of_gt (by linarith))) a2.le (by linarith)
      linarith
    · by_contra hcon
      have hle : r Q' + Q' ≤ r Q + Q := not_lt.1 hcon
      have g1 : G (r Q) < G (r Q') :=
        P247a58c8.strict_left G hcv (hstr _ (ne_of_lt (by linarith))) (by linarith) a1.le
      have g2 : G (r Q' + Q') ≤ G (r Q + Q) := by
        rcases eq_or_lt_of_le hle with h1 | h1
        · rw [h1]
        · exact (P247a58c8.strict_right G hcv (hstr _ (ne_of_gt a2)) b2.le h1).le
      linarith
  · -- r Q ≤ y0 + G y0 / p - h / (h + p) * Q
    have bnd : ∀ Q, 0 < Q → r Q ≤ y0 + G y0 / p - h / (h + p) * Q := by
      intro Q hQ
      obtain ⟨a1, a2⟩ := pos Q hQ
      have e := bal Q hQ
      obtain ⟨l1, -⟩ := P247a58c8.nv_lb hM (r Q + Q)
      obtain ⟨-, l2⟩ := P247a58c8.nv_lb hM (r Q)
      have s := P247a58c8.nv_slope_l hM a1.le
      rw [← hGdef] at l1 l2 s
      rw [e] at l1
      have key : h * p * Q ≤ (h + p) * G (r Q) := by nlinarith
      have key2 : h * Q ≤ (h + p) * (G y0 / p + (y0 - r Q)) := by
        have : G (r Q) ≤ G y0 + p * (y0 - r Q) := by linarith
        have e2 : (h + p) * (G y0 / p + (y0 - r Q)) * p = (h + p) * (G y0 + p * (y0 - r Q)) := by
          field_simp
        nlinarith
      have e3 : h / (h + p) * Q = h * Q / (h + p) := by ring
      rw [e3]
      have : h * Q / (h + p) ≤ G y0 / p + (y0 - r Q) := by
        rw [div_le_iff₀ hhp]; linarith
      linarith
    have lim : Tendsto (fun Q : ℝ => y0 + G y0 / p - h / (h + p) * Q) atTop atBot := by
      have h1 : Tendsto (fun Q : ℝ => h / (h + p) * Q) atTop atTop :=
        tendsto_id.const_mul_atTop (div_pos hh hhp)
      have h2 := tendsto_neg_atTop_atBot.comp h1
      have h3 := tendsto_atBot_add_const_left atTop (y0 + G y0 / p) h2
      refine h3.congr fun Q => ?_
      simp only [Function.comp]
      ring
    refine tendsto_atBot_mono' atTop ?_ lim
    filter_upwards [eventually_gt_atTop 0] with Q hQ
    exact bnd Q hQ
  · have bnd : ∀ Q, 0 < Q → y0 - G y0 / h + p / (h + p) * Q ≤ r Q + Q := by
      intro Q hQ
      obtain ⟨a1, a2⟩ := pos Q hQ
      have e := bal Q hQ
      obtain ⟨l1, -⟩ := P247a58c8.nv_lb hM (r Q + Q)
      obtain ⟨-, l2⟩ := P247a58c8.nv_lb hM (r Q)
      have s := P247a58c8.nv_slope_r hM a2.le
      rw [← hGdef] at l1 l2 s
      rw [← e] at l2
      have key : h * p * Q ≤ (h + p) * G (r Q + Q) := by nlinarith
      have key2 : p * Q ≤ (h + p) * (G y0 / h + (r Q + Q - y0)) := by
        have : G (r Q + Q) ≤ G y0 + h * (r Q + Q - y0) := by linarith
        have e2 : (h + p) * (G y0 / h + (r Q + Q - y0)) * h =
            (h + p) * (G y0 + h * (r Q + Q - y0)) := by
          field_simp
        nlinarith
      have e3 : p / (h + p) * Q = p * Q / (h + p) := by ring
      rw [e3]
      have : p * Q / (h + p) ≤ G y0 / h + (r Q + Q - y0) := by
        rw [div_le_iff₀ hhp]; linarith
      linarith
    have lim : Tendsto (fun Q : ℝ => y0 - G y0 / h + p / (h + p) * Q) atTop atTop := by
      have h1 : Tendsto (fun Q : ℝ => p / (h + p) * Q) atTop atTop :=
        tendsto_id.const_mul_atTop (div_pos hp hhp)
      exact tendsto_atTop_add_const_left atTop (y0 - G y0 / h) h1
    refine tendsto_atTop_mono' atTop ?_ lim
    filter_upwards [eventually_gt_atTop 0] with Q hQ
    exact bnd Q hQ

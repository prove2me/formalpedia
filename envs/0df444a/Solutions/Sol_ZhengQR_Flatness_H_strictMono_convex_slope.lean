-- Prove2me | solution 1 for ZhengQR.Flatness.H_strictMono_convex_slope
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T07:19:53.912609+00:00
-- url     : https://prove2.me/submissions/2d231dd7-5d1d-46c0-ad99-229773c5e363

import Mathlib
import Definitions.Def_ZhengQR_Flatness_QRModel

set_option autoImplicit false

namespace Ffd5c008

open ZhengQR.Flatness MeasureTheory

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
    Hfun G lam K Q = G (optReorder G lam K Q) ∧
      G (optReorder G lam K Q + Q) = G (optReorder G lam K Q) := by
  obtain ⟨r0, hr0⟩ := exists_min G hc hcv hy0 hQ.le
  have hex : ∃ r, IsOptReorder G lam K Q r := ⟨r0, (opt_iff G lam K Q r0 hQ).2 hr0⟩
  have hspec : IsOptReorder G lam K Q (optReorder G lam K Q) := by
    unfold optReorder; rw [dif_pos hex]; exact hex.choose_spec
  refine ⟨?_, balance_of_min G hc ((opt_iff G lam K Q _ hQ).1 hspec)⟩
  unfold Hfun; rw [if_pos hQ]

lemma minPoint_spec (G : ℝ → ℝ) {y0 : ℝ} (hy0 : ∀ z, G y0 ≤ G z) :
    ∀ z, G (minPoint G) ≤ G z := by
  have hex : ∃ y, ∀ z, G y ≤ G z := ⟨y0, hy0⟩
  unfold minPoint; rw [dif_pos hex]; exact hex.choose_spec

lemma H_zero (G : ℝ → ℝ) (lam K : ℝ) : Hfun G lam K 0 = G (minPoint G) := by
  unfold Hfun; rw [if_neg (lt_irrefl 0)]

lemma Hwin (G : ℝ → ℝ) (hc : Continuous G) (hcv : ConvexOn ℝ Set.univ G) {y0 : ℝ}
    (hy0 : ∀ z, G y0 ≤ G z) (lam K Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ r, Hfun G lam K Q = G r ∧ G (r + Q) = G r := by
  rcases eq_or_lt_of_le hQ with h | h
  · subst h
    exact ⟨minPoint G, H_zero G lam K, by rw [add_zero]⟩
  · exact ⟨_, H_pos G hc hcv hy0 lam K Q h⟩

lemma Hle (G : ℝ → ℝ) (hc : Continuous G) (hcv : ConvexOn ℝ Set.univ G) {y0 : ℝ}
    (hy0 : ∀ z, G y0 ≤ G z) (lam K Q : ℝ) (hQ : 0 ≤ Q) (r : ℝ) :
    Hfun G lam K Q ≤ max (G r) (G (r + Q)) := by
  rcases eq_or_lt_of_le hQ with h | h
  · subst h
    rw [H_zero]
    exact (minPoint_spec G hy0 r).trans (le_max_left _ _)
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
    ((integrable_const |y|).add M.integrable.abs).const_mul (M.h + M.p)
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
    newsvendorCost M.h M.p M.μ y2 - newsvendorCost M.h M.p M.μ y1 ≤ M.h * (y2 - y1) := by
  have := M.isProb
  have hh := M.h_pos
  have hp := M.p_pos
  have key : newsvendorCost M.h M.p M.μ y2 ≤
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
    newsvendorCost M.h M.p M.μ y1 - newsvendorCost M.h M.p M.μ y2 ≤ M.p * (y2 - y1) := by
  have := M.isProb
  have hh := M.h_pos
  have hp := M.p_pos
  have key : newsvendorCost M.h M.p M.μ y1 ≤
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

lemma nv_convex : ConvexOn ℝ Set.univ (newsvendorCost M.h M.p M.μ) := by
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

lemma nv_cont : Continuous (newsvendorCost M.h M.p M.μ) := by
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
    M.h * (y - M.lam * M.L) ≤ newsvendorCost M.h M.p M.μ y ∧
      M.p * (M.lam * M.L - y) ≤ newsvendorCost M.h M.p M.μ y := by
  have := M.isProb
  have hh := M.h_pos
  have hp := M.p_pos
  have i1 : Integrable (fun x => M.h * y - M.h * x) M.μ :=
    (integrable_const _).sub (M.integrable.const_mul _)
  have i2 : Integrable (fun x => M.p * x - M.p * y) M.μ :=
    (M.integrable.const_mul _).sub (integrable_const _)
  have e1 : ∫ x, (M.h * y - M.h * x) ∂M.μ = M.h * (y - M.lam * M.L) := by
    rw [integral_sub (integrable_const _) (M.integrable.const_mul _), integral_const,
      probReal_univ, one_smul, integral_const_mul, M.mean_eq]
    ring
  have e2 : ∫ x, (M.p * x - M.p * y) ∂M.μ = M.p * (M.lam * M.L - y) := by
    rw [integral_sub (M.integrable.const_mul _) (integrable_const _), integral_const,
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

end Ffd5c008

open ZhengQR.Flatness Filter Topology in
theorem solution (M : QRModel) :
    StrictMonoOn M.H (Set.Ici 0) ∧ ConvexOn ℝ (Set.Ici 0) M.H ∧
      Tendsto (fun Q : ℝ => M.H Q / Q) atTop (𝓝 (M.h * M.p / (M.h + M.p))) ∧
      ∀ Q₁ Q₂ : ℝ, 0 ≤ Q₁ → Q₁ ≤ Q₂ →
        M.H Q₂ - M.H Q₁ ≤ M.h * M.p / (M.h + M.p) * (Q₂ - Q₁) := by
  set G := newsvendorCost M.h M.p M.μ with hGdef
  have hH : ∀ Q, M.H Q = Hfun G M.lam M.K Q := fun Q => rfl
  have hc : Continuous G := Ffd5c008.nv_cont M
  have hcv : ConvexOn ℝ Set.univ G := Ffd5c008.nv_convex M
  obtain ⟨y0, hy0, huniq⟩ := M.unique_min
  have hh := M.h_pos
  have hp := M.p_pos
  have hhp : 0 < M.h + M.p := add_pos hh hp
  have win := Ffd5c008.Hwin G hc hcv hy0 M.lam M.K
  have hle := Ffd5c008.Hle G hc hcv hy0 M.lam M.K
  -- chord bound
  have chord : ∀ Q₁ Q₂ : ℝ, 0 ≤ Q₁ → Q₁ ≤ Q₂ →
      M.H Q₂ - M.H Q₁ ≤ M.h * M.p / (M.h + M.p) * (Q₂ - Q₁) := by
    intro Q₁ Q₂ hQ1 hQ12
    obtain ⟨r1, e1, e2⟩ := win Q₁ hQ1
    set d := Q₂ - Q₁ with hd
    have hd0 : 0 ≤ d := by linarith
    have k := hle Q₂ (by linarith) (r1 - M.h * d / (M.h + M.p))
    have hpt : r1 - M.h * d / (M.h + M.p) + Q₂ = (r1 + Q₁) + M.p * d / (M.h + M.p) := by
      field_simp; rw [hd]; ring
    rw [hpt] at k
    have s1 := Ffd5c008.nv_slope_l M
      (show r1 - M.h * d / (M.h + M.p) ≤ r1 by
        have : 0 ≤ M.h * d / (M.h + M.p) := by positivity
        linarith)
    have s2 := Ffd5c008.nv_slope_r M
      (show r1 + Q₁ ≤ (r1 + Q₁) + M.p * d / (M.h + M.p) by
        have : 0 ≤ M.p * d / (M.h + M.p) := by positivity
        linarith)
    have c1 : M.p * (r1 - (r1 - M.h * d / (M.h + M.p))) = M.h * M.p / (M.h + M.p) * d := by
      field_simp; ring
    have c2 : M.h * ((r1 + Q₁) + M.p * d / (M.h + M.p) - (r1 + Q₁)) =
        M.h * M.p / (M.h + M.p) * d := by
      field_simp; ring
    rw [hH, hH, e1]
    rw [← hGdef] at s1 s2
    have := max_le_iff.1 (le_refl (max (G (r1 - M.h * d / (M.h + M.p)))
      (G (r1 + Q₁ + M.p * d / (M.h + M.p)))))
    rcases le_total (G (r1 - M.h * d / (M.h + M.p))) (G (r1 + Q₁ + M.p * d / (M.h + M.p)))
      with hm | hm
    · rw [max_eq_right hm] at k; linarith
    · rw [max_eq_left hm] at k; linarith
  refine ⟨?_, ?_, ?_, chord⟩
  · -- strict monotonicity
    intro Q₁ hQ1 Q₂ hQ2 h12
    simp only [Set.mem_Ici] at hQ1 hQ2
    have hQ2p : 0 < Q₂ := by linarith
    obtain ⟨e1, e2⟩ := Ffd5c008.H_pos G hc hcv hy0 M.lam M.K Q₂ hQ2p
    set r2 := optReorder G M.lam M.K Q₂ with hr2
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
      · have := Ffd5c008.outside_left G hcv hQ2p e2 h; linarith
      · exact h
    have hy2 : y0 < r2 + Q₂ := by
      by_contra hcon
      have := Ffd5c008.outside_right G hcv hQ2p e2 (not_lt.1 hcon)
      linarith
    set d := (Q₂ - Q₁) / 2 with hd
    have hd0 : 0 < d := by rw [hd]; linarith
    have k := hle Q₁ hQ1 (r2 + d)
    have i1 := Ffd5c008.inside_lt G hcv e2 hlt hy1 hy2 (z := r2 + d) (by linarith)
      (by rw [hd]; linarith)
    have i2 := Ffd5c008.inside_lt G hcv e2 hlt hy1 hy2 (z := r2 + d + Q₁) (by linarith)
      (by rw [hd]; linarith)
    rw [hH, hH, e1]
    exact lt_of_le_of_lt k (max_lt i1 i2)
  · -- convexity
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
    rw [hH, hH, hH, ex1, ey1]
    rw [ex2, ey2] at c2
    exact k.trans (max_le c1 c2)
  · -- slope limit
    have lb : ∀ Q, 0 ≤ Q → M.h * M.p / (M.h + M.p) * Q ≤ M.H Q := by
      intro Q hQ
      obtain ⟨r, e1, e2⟩ := win Q hQ
      obtain ⟨l1, -⟩ := Ffd5c008.nv_lb M (r + Q)
      obtain ⟨-, l2⟩ := Ffd5c008.nv_lb M r
      rw [← hGdef, e2] at l1
      rw [← hGdef] at l2
      rw [hH, e1, div_mul_eq_mul_div, div_le_iff₀ hhp]
      nlinarith
    set c := M.h * M.p / (M.h + M.p) with hc_def
    have upper : Tendsto (fun Q : ℝ => c + M.H 0 * Q⁻¹) atTop (𝓝 c) := by
      have := (tendsto_inv_atTop_zero.const_mul (M.H 0)).const_add c
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds upper ?_ ?_
    · filter_upwards [Filter.eventually_gt_atTop 0] with Q hQ
      rw [le_div_iff₀ hQ]
      exact lb Q hQ.le
    · filter_upwards [Filter.eventually_gt_atTop 0] with Q hQ
      have := chord 0 Q le_rfl hQ.le
      rw [div_le_iff₀ hQ, add_mul]
      have e : M.H 0 * Q⁻¹ * Q = M.H 0 := by field_simp
      rw [e]
      linarith

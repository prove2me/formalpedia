-- Prove2me | solution 1 for ZhengQR.OrderQty.integral_A_chain
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T13:24:39.400811+00:00
-- url     : https://prove2.me/submissions/ca3d97b8-10ff-400b-9b15-e87a3837a3a2

import Mathlib
import Definitions.Def_ZhengQR_OrderQty_newsvendorCost
import Definitions.Def_ZhengQR_OrderQty_qrMachinery

set_option autoImplicit false

namespace X7e438c33

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

lemma integ (hμ : IsLeadtimeDemand lam L μ) (hh : 0 < h) (hp : 0 < p) (y : ℝ) :
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

lemma nv_slope_r (hμ : IsLeadtimeDemand lam L μ) (hh : 0 < h) (hp : 0 < p) {y1 y2 : ℝ}
    (h12 : y1 ≤ y2) :
    newsvendorCost h p μ y2 - newsvendorCost h p μ y1 ≤ h * (y2 - y1) := by
  have := hμ.isProb
  have key : newsvendorCost h p μ y2 ≤
      ∫ x, ((h * max (y1 - x) 0 + p * max (x - y1) 0) + h * (y2 - y1)) ∂μ := by
    unfold newsvendorCost
    refine integral_mono (integ hμ hh hp y2) ((integ hμ hh hp y1).add (integrable_const _))
      (fun x => ?_)
    have a1 : max (y2 - x) 0 ≤ max (y1 - x) 0 + (y2 - y1) :=
      max_le (by linarith [le_max_left (y1 - x) 0]) (by linarith [le_max_right (y1 - x) 0])
    have a2 : max (x - y2) 0 ≤ max (x - y1) 0 :=
      max_le (by linarith [le_max_left (x - y1) 0]) (le_max_right _ _)
    simp only
    nlinarith
  rw [integral_add (integ hμ hh hp y1) (integrable_const _), integral_const, probReal_univ,
    one_smul] at key
  unfold newsvendorCost at key ⊢
  linarith

lemma nv_slope_l (hμ : IsLeadtimeDemand lam L μ) (hh : 0 < h) (hp : 0 < p) {y1 y2 : ℝ}
    (h12 : y1 ≤ y2) :
    newsvendorCost h p μ y1 - newsvendorCost h p μ y2 ≤ p * (y2 - y1) := by
  have := hμ.isProb
  have key : newsvendorCost h p μ y1 ≤
      ∫ x, ((h * max (y2 - x) 0 + p * max (x - y2) 0) + p * (y2 - y1)) ∂μ := by
    unfold newsvendorCost
    refine integral_mono (integ hμ hh hp y1) ((integ hμ hh hp y2).add (integrable_const _))
      (fun x => ?_)
    have a1 : max (x - y1) 0 ≤ max (x - y2) 0 + (y2 - y1) :=
      max_le (by linarith [le_max_left (x - y2) 0]) (by linarith [le_max_right (x - y2) 0])
    have a2 : max (y1 - x) 0 ≤ max (y2 - x) 0 :=
      max_le (by linarith [le_max_left (y2 - x) 0]) (le_max_right _ _)
    simp only
    nlinarith
  rw [integral_add (integ hμ hh hp y2) (integrable_const _), integral_const, probReal_univ,
    one_smul] at key
  unfold newsvendorCost at key ⊢
  linarith

lemma nv_convex (hμ : IsLeadtimeDemand lam L μ) (hh : 0 < h) (hp : 0 < p) :
    ConvexOn ℝ Set.univ (newsvendorCost h p μ) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  unfold newsvendorCost
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((integ hμ hh hp x).const_mul a) ((integ hμ hh hp y).const_mul b)]
  refine integral_mono (integ hμ hh hp _)
    (((integ hμ hh hp x).const_mul a).add ((integ hμ hh hp y).const_mul b)) (fun t => ?_)
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

lemma nv_cont (hμ : IsLeadtimeDemand lam L μ) (hh : 0 < h) (hp : 0 < p) :
    Continuous (newsvendorCost h p μ) := by
  refine (LipschitzWith.of_le_add_mul' (h + p) (fun x y => ?_)).continuous
  rw [Real.dist_eq]
  rcases le_total y x with hxy | hxy
  · have := nv_slope_r hμ hh hp hxy
    have : h * (x - y) ≤ (h + p) * |x - y| := by
      rw [abs_of_nonneg (by linarith)]; nlinarith
    linarith
  · have := nv_slope_l hμ hh hp hxy
    have : p * (y - x) ≤ (h + p) * |x - y| := by
      rw [abs_of_nonpos (by linarith)]; nlinarith
    linarith

lemma nv_lb (hμ : IsLeadtimeDemand lam L μ) (hh : 0 < h) (hp : 0 < p) (y : ℝ) :
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
    refine integral_mono i1 (integ hμ hh hp y) (fun x => ?_)
    have b1 := le_max_left (y - x) 0
    have b2 : 0 ≤ max (x - y) 0 := le_max_right _ _
    simp only
    nlinarith
  · rw [← e2]
    unfold newsvendorCost
    refine integral_mono i2 (integ hμ hh hp y) (fun x => ?_)
    have b1 := le_max_left (x - y) 0
    have b2 : 0 ≤ max (y - x) 0 := le_max_right _ _
    simp only
    nlinarith

end NV

end X7e438c33

open MeasureTheory Filter Topology ZhengQR.OrderQty in
theorem X7e438c33_mainH
    {lam L h p : ℝ} {μ : Measure ℝ}
    (hlam : 0 < lam) (hL : 0 < L) (hh : 0 < h) (hp : 0 < p)
    (hμ : IsLeadtimeDemand lam L μ)
    (hG : ∃! y : ℝ, IsMinimizer (newsvendorCost h p μ) y) :
    StrictMonoOn (Hfun (newsvendorCost h p μ)) (Set.Ici 0) ∧
    ConvexOn ℝ (Set.Ici 0) (Hfun (newsvendorCost h p μ)) ∧
    Tendsto (fun Q => Hfun (newsvendorCost h p μ) Q / Q) atTop (𝓝 (h * p / (h + p))) ∧
    ∀ Q Q' : ℝ, 0 ≤ Q → Q < Q' →
      Hfun (newsvendorCost h p μ) Q' - Hfun (newsvendorCost h p μ) Q ≤
        h * p / (h + p) * (Q' - Q) := by
  set G := newsvendorCost h p μ with hGdef
  have hc : Continuous G := X7e438c33.nv_cont hμ hh hp
  have hcv : ConvexOn ℝ Set.univ G := X7e438c33.nv_convex hμ hh hp
  obtain ⟨y0, hy0, huniq⟩ := hG
  have hy0' : ∀ z, G y0 ≤ G z := hy0
  have hhp : 0 < h + p := add_pos hh hp
  have win := X7e438c33.Hwin G hc hcv hy0'
  have hle := X7e438c33.Hle G hc hcv hy0'
  -- chord bound
  have chord : ∀ Q₁ Q₂ : ℝ, 0 ≤ Q₁ → Q₁ ≤ Q₂ →
      Hfun G Q₂ - Hfun G Q₁ ≤ h * p / (h + p) * (Q₂ - Q₁) := by
    intro Q₁ Q₂ hQ1 hQ12
    obtain ⟨r1, e1, e2⟩ := win Q₁ hQ1
    set d := Q₂ - Q₁ with hd
    have hd0 : 0 ≤ d := by linarith
    have k := hle Q₂ (by linarith) (r1 - h * d / (h + p))
    have hpt : r1 - h * d / (h + p) + Q₂ = (r1 + Q₁) + p * d / (h + p) := by
      field_simp; rw [hd]; ring
    rw [hpt] at k
    have s1 := X7e438c33.nv_slope_l hμ hh hp
      (show r1 - h * d / (h + p) ≤ r1 by
        have : 0 ≤ h * d / (h + p) := by positivity
        linarith)
    have s2 := X7e438c33.nv_slope_r hμ hh hp
      (show r1 + Q₁ ≤ (r1 + Q₁) + p * d / (h + p) by
        have : 0 ≤ p * d / (h + p) := by positivity
        linarith)
    have c1 : p * (r1 - (r1 - h * d / (h + p))) = h * p / (h + p) * d := by
      field_simp; ring
    have c2 : h * ((r1 + Q₁) + p * d / (h + p) - (r1 + Q₁)) =
        h * p / (h + p) * d := by
      field_simp; ring
    rw [e1]
    rw [← hGdef] at s1 s2
    rcases le_total (G (r1 - h * d / (h + p))) (G (r1 + Q₁ + p * d / (h + p)))
      with hm | hm
    · rw [max_eq_right hm] at k; linarith
    · rw [max_eq_left hm] at k; linarith
  refine ⟨?_, ?_, ?_, fun Q Q' hQ hQQ => chord Q Q' hQ hQQ.le⟩
  · -- strict monotonicity
    intro Q₁ hQ1 Q₂ hQ2 h12
    simp only [Set.mem_Ici] at hQ1 hQ2
    have hQ2p : 0 < Q₂ := by linarith
    obtain ⟨e1, e2⟩ := X7e438c33.H_pos G hc hcv hy0' Q₂ hQ2p
    set r2 := optReorder G Q₂ with hr2
    have hlt : G y0 < G r2 := by
      rcases lt_or_ge (G y0) (G r2) with h' | h'
      · exact h'
      · exfalso
        have m1 : ∀ z, G r2 ≤ G z := fun z => h'.trans (hy0' z)
        have m2 : ∀ z, G (r2 + Q₂) ≤ G z := fun z => by rw [e2]; exact m1 z
        have := huniq _ m1
        have := huniq _ m2
        linarith
    have hy1 : r2 < y0 := by
      rcases le_or_gt y0 r2 with h' | h'
      · have := X7e438c33.outside_left G hcv hQ2p e2 h'; linarith
      · exact h'
    have hy2 : y0 < r2 + Q₂ := by
      by_contra hcon
      have := X7e438c33.outside_right G hcv hQ2p e2 (not_lt.1 hcon)
      linarith
    set d := (Q₂ - Q₁) / 2 with hd
    have hd0 : 0 < d := by rw [hd]; linarith
    have k := hle Q₁ hQ1 (r2 + d)
    have i1 := X7e438c33.inside_lt G hcv e2 hlt hy1 hy2 (z := r2 + d) (by linarith)
      (by rw [hd]; linarith)
    have i2 := X7e438c33.inside_lt G hcv e2 hlt hy1 hy2 (z := r2 + d + Q₁) (by linarith)
      (by rw [hd]; linarith)
    rw [e1]
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
    rw [ex1, ey1]
    rw [ex2, ey2] at c2
    exact k.trans (max_le c1 c2)
  · -- slope limit
    have lb : ∀ Q, 0 ≤ Q → h * p / (h + p) * Q ≤ Hfun G Q := by
      intro Q hQ
      obtain ⟨r, e1, e2⟩ := win Q hQ
      obtain ⟨l1, -⟩ := X7e438c33.nv_lb hμ hh hp (r + Q)
      obtain ⟨-, l2⟩ := X7e438c33.nv_lb hμ hh hp r
      rw [← hGdef, e2] at l1
      rw [← hGdef] at l2
      rw [e1, div_mul_eq_mul_div, div_le_iff₀ hhp]
      nlinarith
    set c := h * p / (h + p) with hc_def
    have upper : Tendsto (fun Q : ℝ => c + Hfun G 0 * Q⁻¹) atTop (𝓝 c) := by
      have := (tendsto_inv_atTop_zero.const_mul (Hfun G 0)).const_add c
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds upper ?_ ?_
    · filter_upwards [Filter.eventually_gt_atTop 0] with Q hQ
      rw [le_div_iff₀ hQ]
      exact lb Q hQ.le
    · filter_upwards [Filter.eventually_gt_atTop 0] with Q hQ
      have := chord 0 Q le_rfl hQ.le
      rw [div_le_iff₀ hQ, add_mul]
      have e : Hfun G 0 * Q⁻¹ * Q = Hfun G 0 := by field_simp
      rw [e]
      linarith

namespace P7fefa2a3

open ZhengQR.OrderQty

lemma eoq_cont (lam L h p : ℝ) : Continuous (eoqCost lam L h p) := by
  unfold eoqCost; fun_prop

lemma eoq_nonneg (lam L h p : ℝ) (hh : 0 < h) (hp : 0 < p) (y : ℝ) :
    0 ≤ eoqCost lam L h p y := by
  unfold eoqCost
  exact add_nonneg (mul_nonneg hh.le (le_max_right _ _)) (mul_nonneg hp.le (le_max_right _ _))

lemma eoq_zero_iff (lam L h p : ℝ) (hh : 0 < h) (hp : 0 < p) (y : ℝ)
    (hy : eoqCost lam L h p y ≤ 0) : y = lam * L := by
  unfold eoqCost at hy
  rcases lt_trichotomy y (lam * L) with h1 | h1 | h1
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)] at hy
    nlinarith [mul_pos hp (sub_pos.2 h1)]
  · exact h1
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)] at hy
    nlinarith [mul_pos hh (sub_pos.2 h1)]

lemma int_left (lam L h p a b : ℝ) (hab : a ≤ b) (hb : b ≤ lam * L) :
    ∫ y in a..b, eoqCost lam L h p y = p * ((lam * L - a) ^ 2 - (lam * L - b) ^ 2) / 2 := by
  have e : ∫ y in a..b, eoqCost lam L h p y = ∫ y in a..b, (p * (lam * L) - p * y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hab] at hy
    simp only [eoqCost]
    rw [max_eq_right (by linarith [hy.2]), max_eq_left (by linarith [hy.2])]
    ring
  rw [e, intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_id]
  simp only [smul_eq_mul]
  ring

lemma int_right (lam L h p a b : ℝ) (hab : a ≤ b) (ha : lam * L ≤ a) :
    ∫ y in a..b, eoqCost lam L h p y = h * ((b - lam * L) ^ 2 - (a - lam * L) ^ 2) / 2 := by
  have e : ∫ y in a..b, eoqCost lam L h p y = ∫ y in a..b, (h * y - h * (lam * L)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hab] at hy
    simp only [eoqCost]
    rw [max_eq_left (by linarith [hy.1]), max_eq_right (by linarith [hy.1])]
    ring
  rw [e, intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_id]
  simp only [smul_eq_mul]
  ring

/-- Window characterisation. -/
lemma window (lam L h p Q r : ℝ) (hh : 0 < h) (hp : 0 < p) (hQ : 0 < Q) :
    h * p * Q ^ 2 ≤ (h + p) * (2 * ∫ y in r..r + Q, eoqCost lam L h p y) ∧
    ((h + p) * (2 * ∫ y in r..r + Q, eoqCost lam L h p y) ≤ h * p * Q ^ 2 ↔
      (h + p) * (r - lam * L) + h * Q = 0) := by
  rcases le_or_gt (r + Q) (lam * L) with h1 | h1
  · rw [int_left lam L h p r (r + Q) (by linarith) h1]
    have ht : 0 ≤ lam * L - r - Q := by linarith
    have k1 : 0 ≤ 2 * p * Q * (h + p) * (lam * L - r - Q) := by
      have := mul_nonneg (mul_nonneg (mul_nonneg (mul_pos (by norm_num : (0:ℝ) < 2) hp).le hQ.le)
        (add_pos hh hp).le) ht
      linarith
    have k2 : 0 < p * p * (Q * Q) := mul_pos (mul_pos hp hp) (mul_pos hQ hQ)
    have eq : (h + p) * (2 * (p * ((lam * L - r) ^ 2 - (lam * L - (r + Q)) ^ 2) / 2))
        - h * p * Q ^ 2 = 2 * p * Q * (h + p) * (lam * L - r - Q) + p * p * (Q * Q) := by ring
    refine ⟨by linarith, ?_⟩
    constructor
    · intro H; exfalso; linarith
    · intro H; exfalso
      have : (h + p) * (r - lam * L) + h * Q ≤ -(p * Q) := by nlinarith
      nlinarith [mul_pos hp hQ]
  · rcases le_or_gt (lam * L) r with h2 | h2
    · rw [int_right lam L h p r (r + Q) (by linarith) h2]
      have ht : 0 ≤ r - lam * L := by linarith
      have k1 : 0 ≤ 2 * h * Q * (h + p) * (r - lam * L) := by
        have := mul_nonneg (mul_nonneg (mul_nonneg (mul_pos (by norm_num : (0:ℝ) < 2) hh).le hQ.le)
          (add_pos hh hp).le) ht
        linarith
      have k2 : 0 < h * h * (Q * Q) := mul_pos (mul_pos hh hh) (mul_pos hQ hQ)
      have eq : (h + p) * (2 * (h * ((r + Q - lam * L) ^ 2 - (r - lam * L) ^ 2) / 2))
          - h * p * Q ^ 2 = 2 * h * Q * (h + p) * (r - lam * L) + h * h * (Q * Q) := by ring
      refine ⟨by linarith, ?_⟩
      constructor
      · intro H; exfalso; linarith
      · intro H; exfalso
        have : 0 ≤ (h + p) * (r - lam * L) := mul_nonneg (add_pos hh hp).le ht
        nlinarith [mul_pos hh hQ]
    · have hc := eoq_cont lam L h p
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := lam * L)
        (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
        int_left lam L h p r (lam * L) h2.le le_rfl,
        int_right lam L h p (lam * L) (r + Q) h1.le le_rfl]
      have eq : (h + p) * (2 * (p * ((lam * L - r) ^ 2 - (lam * L - lam * L) ^ 2) / 2 +
          h * ((r + Q - lam * L) ^ 2 - (lam * L - lam * L) ^ 2) / 2)) - h * p * Q ^ 2
          = ((h + p) * (r - lam * L) + h * Q) ^ 2 := by ring
      refine ⟨by nlinarith [sq_nonneg ((h + p) * (r - lam * L) + h * Q)], ?_⟩
      constructor
      · intro H
        have h0 : ((h + p) * (r - lam * L) + h * Q) ^ 2 ≤ 0 := by linarith
        have := le_antisymm h0 (sq_nonneg _)
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      · intro H
        rw [H] at eq
        linarith

lemma reorder_eq (lam L h p Q : ℝ) (hh : 0 < h) (hp : 0 < p) (hQ : 0 < Q) :
    optReorder (eoqCost lam L h p) Q = lam * L - h / (h + p) * Q := by
  have hhp : 0 < h + p := add_pos hh hp
  set r0 := lam * L - h / (h + p) * Q with hr0def
  have hr0 : (h + p) * (r0 - lam * L) + h * Q = 0 := by
    rw [hr0def]; field_simp; ring
  have w0 := (window lam L h p Q r0 hh hp hQ).2.mpr hr0
  have hopt : ∀ r' : ℝ, (∫ y in r0..r0 + Q, eoqCost lam L h p y) ≤
      ∫ y in r'..r' + Q, eoqCost lam L h p y := by
    intro r'
    have w1 := (window lam L h p Q r' hh hp hQ).1
    have : (h + p) * (2 * ∫ y in r0..r0 + Q, eoqCost lam L h p y) ≤
        (h + p) * (2 * ∫ y in r'..r' + Q, eoqCost lam L h p y) := le_trans w0 w1
    have := le_of_mul_le_mul_left this hhp
    linarith
  have hex : ∃ r, ∀ r' : ℝ, (∫ y in r..r + Q, eoqCost lam L h p y) ≤
      ∫ y in r'..r' + Q, eoqCost lam L h p y := ⟨r0, hopt⟩
  unfold optReorder
  rw [dif_pos hex]
  have hs := hex.choose_spec
  have h1 := hs r0
  have h2 : (h + p) * (2 * ∫ y in hex.choose..hex.choose + Q, eoqCost lam L h p y) ≤ h * p * Q ^ 2 := by
    have : (h + p) * (2 * ∫ y in hex.choose..hex.choose + Q, eoqCost lam L h p y) ≤
        (h + p) * (2 * ∫ y in r0..r0 + Q, eoqCost lam L h p y) :=
      mul_le_mul_of_nonneg_left (by linarith) hhp.le
    linarith
  have h3 := (window lam L h p Q hex.choose hh hp hQ).2.mp h2
  have h4 : (h + p) * (hex.choose - r0) = 0 := by linarith
  rcases mul_eq_zero.1 h4 with h5 | h5
  · linarith
  · linarith

lemma window_val (lam L h p Q : ℝ) (hh : 0 < h) (hp : 0 < p) (hQ : 0 < Q) :
    (∫ y in (lam * L - h / (h + p) * Q)..(lam * L - h / (h + p) * Q) + Q, eoqCost lam L h p y)
      = h * p * Q ^ 2 / (2 * (h + p)) := by
  have hhp : 0 < h + p := add_pos hh hp
  have hr0 : (h + p) * ((lam * L - h / (h + p) * Q) - lam * L) + h * Q = 0 := by
    field_simp; ring
  have w := window lam L h p Q (lam * L - h / (h + p) * Q) hh hp hQ
  have e := le_antisymm (w.2.mpr hr0) w.1
  rw [eq_div_iff (by positivity)]
  linarith

lemma optCost_eq (lam L K h p Q : ℝ) (hh : 0 < h) (hp : 0 < p) (hQ : 0 < Q) :
    optCost (eoqCost lam L h p) lam K Q = (lam * K + h * p * Q ^ 2 / (2 * (h + p))) / Q := by
  unfold optCost qrCost
  rw [reorder_eq lam L h p Q hh hp hQ, window_val lam L h p Q hh hp hQ]

lemma minPoint_eq (lam L h p : ℝ) (hh : 0 < h) (hp : 0 < p) :
    minPoint (eoqCost lam L h p) = lam * L := by
  have hm : eoqCost lam L h p (lam * L) = 0 := by simp [eoqCost]
  have hex : ∃ y, IsMinimizer (eoqCost lam L h p) y :=
    ⟨lam * L, fun z => by rw [hm]; exact eoq_nonneg lam L h p hh hp z⟩
  unfold minPoint
  rw [dif_pos hex]
  have := hex.choose_spec (lam * L)
  rw [hm] at this
  exact eoq_zero_iff lam L h p hh hp _ this


lemma Hd_eq (lam L h p : ℝ) (hh : 0 < h) (hp : 0 < p) (Q : ℝ) (hQ : 0 ≤ Q) :
    Hfun (eoqCost lam L h p) Q = h * p / (h + p) * Q := by
  have hm : eoqCost lam L h p (lam * L) = 0 := by simp [eoqCost]
  rcases hQ.lt_or_eq with hQ | hQ
  · unfold Hfun
    rw [if_pos hQ, reorder_eq lam L h p Q hh hp hQ]
    unfold eoqCost
    have hpos : 0 < h / (h + p) * Q := by positivity
    have e1 : lam * L - h / (h + p) * Q - lam * L = -(h / (h + p) * Q) := by ring
    have e2 : lam * L - (lam * L - h / (h + p) * Q) = h / (h + p) * Q := by ring
    rw [e1, e2, max_eq_right (by linarith), max_eq_left hpos.le]
    field_simp
    ring
  · subst hQ
    unfold Hfun
    rw [if_neg (lt_irrefl 0), minPoint_eq lam L h p hh hp, hm]
    ring

end P7fefa2a3

open MeasureTheory Filter Topology ZhengQR.OrderQty in
lemma stoch_part
    {lam L h p : ℝ} {μ : Measure ℝ}
    (hlam : 0 < lam) (hL : 0 < L) (hh : 0 < h) (hp : 0 < p)
    (hμ : IsLeadtimeDemand lam L μ)
    (hG : ∃! y : ℝ, IsMinimizer (newsvendorCost h p μ) y) (Q : ℝ) (hQ : 0 ≤ Q) :
      1 / 2 * Q * Hfun (newsvendorCost h p μ) Q ≤ ∫ y in (0 : ℝ)..Q, Hfun (newsvendorCost h p μ) y ∧
      Afun (newsvendorCost h p μ) Q ≤ 1 / 2 * Q * Hfun (newsvendorCost h p μ) Q ∧
      1 / 2 * Q * H0fun (newsvendorCost h p μ) Q ≤ Afun (newsvendorCost h p μ) Q ∧
      (∫ y in (0 : ℝ)..Q, H0fun (newsvendorCost h p μ) y) ≤ 1 / 2 * Q * H0fun (newsvendorCost h p μ) Q := by
  obtain ⟨hmono, hconv, -, chord⟩ := X7e438c33_mainH hlam hL hh hp hμ hG
  set G := newsvendorCost h p μ with hGdef
  have hc : Continuous G := X7e438c33.nv_cont hμ hh hp
  have hcv : ConvexOn ℝ Set.univ G := X7e438c33.nv_convex hμ hh hp
  obtain ⟨y0, hy0, -⟩ := hG
  have hy0' : ∀ z, G y0 ≤ G z := hy0
  have hhp : 0 < h + p := add_pos hh hp
  have win := X7e438c33.Hwin G hc hcv hy0'
  set c := h * p / (h + p) with hc_def
  have lb : ∀ Q, 0 ≤ Q → c * Q ≤ Hfun G Q := by
    intro Q hQ
    obtain ⟨r, e1, e2⟩ := win Q hQ
    obtain ⟨l1, -⟩ := X7e438c33.nv_lb hμ hh hp (r + Q)
    obtain ⟨-, l2⟩ := X7e438c33.nv_lb hμ hh hp r
    rw [← hGdef, e2] at l1
    rw [← hGdef] at l2
    rw [e1, hc_def, div_mul_eq_mul_div, div_le_iff₀ hhp]
    nlinarith
  have H0 : Hfun G 0 = G (minPoint G) := X7e438c33.H_zero G
  have hint : IntervalIntegrable (Hfun G) volume 0 Q := by
    apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le hQ]
    exact (hmono.monotoneOn).mono (fun x hx => hx.1)
  -- key bounds
  have I1 : 1 / 2 * Q * Hfun G Q ≤ ∫ y in (0 : ℝ)..Q, Hfun G y := by
    rcases hQ.lt_or_eq with hQp | hQ0
    · have pt : ∀ y ∈ Set.Icc (0 : ℝ) Q, Hfun G Q / Q * y ≤ Hfun G y := by
        intro y hy
        rcases hy.2.lt_or_eq with hyQ | hyQ
        · have k1 := chord y Q hy.1 hyQ
          have k2 := lb y hy.1
          rw [div_mul_eq_mul_div, div_le_iff₀ hQp]
          nlinarith [mul_le_mul_of_nonneg_left k2 (sub_nonneg.2 hyQ.le),
            mul_le_mul_of_nonneg_left k1 hy.1]
        · subst hyQ
          rw [div_mul_cancel₀ _ hQp.ne']
      have k := intervalIntegral.integral_mono_on (f := fun y => Hfun G Q / Q * y) (g := Hfun G) hQ
        (by apply Continuous.intervalIntegrable; fun_prop) hint pt
      rw [intervalIntegral.integral_const_mul, integral_id] at k
      have e : Hfun G Q / Q * ((Q ^ 2 - 0 ^ 2) / 2) = 1 / 2 * Q * Hfun G Q := by
        field_simp
        ring
      linarith
    · subst hQ0
      simp
  have I2 : (∫ y in (0 : ℝ)..Q, Hfun G y) ≤ 1 / 2 * Q * Hfun G Q + 1 / 2 * Q * Hfun G 0 := by
    rcases hQ.lt_or_eq with hQp | hQ0
    · have pt : ∀ y ∈ Set.Icc (0 : ℝ) Q,
          Hfun G y ≤ Hfun G 0 + (Hfun G Q - Hfun G 0) / Q * y := by
        intro y hy
        have ha : 0 ≤ (Q - y) / Q := div_nonneg (by linarith [hy.2]) hQp.le
        have hb : 0 ≤ y / Q := div_nonneg hy.1 hQp.le
        have hab : (Q - y) / Q + y / Q = 1 := by field_simp; ring
        have k := hconv.2 (Set.mem_Ici.2 (le_refl (0 : ℝ))) (Set.mem_Ici.2 hQ) ha hb hab
        simp only [smul_eq_mul] at k
        have hpt : (Q - y) / Q * 0 + y / Q * Q = y := by
          rw [mul_zero, zero_add, div_mul_cancel₀ _ hQp.ne']
        rw [hpt] at k
        have e : (Q - y) / Q * Hfun G 0 + y / Q * Hfun G Q =
            Hfun G 0 + (Hfun G Q - Hfun G 0) / Q * y := by
          field_simp; ring
        linarith
      have k := intervalIntegral.integral_mono_on (f := Hfun G)
        (g := fun y => Hfun G 0 + (Hfun G Q - Hfun G 0) / Q * y) hQ hint
        (by apply Continuous.intervalIntegrable; fun_prop) pt
      rw [intervalIntegral.integral_add intervalIntegrable_const
        (by apply Continuous.intervalIntegrable; fun_prop),
        intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const,
        smul_eq_mul] at k
      have e : (Q - 0) * Hfun G 0 + (Hfun G Q - Hfun G 0) / Q * ((Q ^ 2 - 0 ^ 2) / 2) =
          1 / 2 * Q * Hfun G Q + 1 / 2 * Q * Hfun G 0 := by
        field_simp; ring
      linarith
    · subst hQ0
      simp
  have IH0 : (∫ y in (0 : ℝ)..Q, H0fun G y) =
      (∫ y in (0 : ℝ)..Q, Hfun G y) - Q * G (minPoint G) := by
    unfold H0fun
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  refine ⟨I1, ?_, ?_, ?_⟩
  · unfold Afun; linarith
  · unfold Afun H0fun; rw [H0] at I2; linarith
  · rw [IH0]; unfold H0fun; rw [H0] at I2; linarith

open MeasureTheory Filter Topology ZhengQR.OrderQty in
lemma det_part {lam L h p : ℝ} (hh : 0 < h) (hp : 0 < p) (Q : ℝ) (hQ : 0 ≤ Q) :
      1 / 2 * Q * Hfun (eoqCost lam L h p) Q = ∫ y in (0 : ℝ)..Q, Hfun (eoqCost lam L h p) y ∧
      Afun (eoqCost lam L h p) Q = 1 / 2 * Q * Hfun (eoqCost lam L h p) Q ∧
      1 / 2 * Q * H0fun (eoqCost lam L h p) Q = Afun (eoqCost lam L h p) Q ∧
      (∫ y in (0 : ℝ)..Q, H0fun (eoqCost lam L h p) y) = 1 / 2 * Q * H0fun (eoqCost lam L h p) Q := by
  have hm : eoqCost lam L h p (lam * L) = 0 := by simp [eoqCost]
  have hmin : eoqCost lam L h p (minPoint (eoqCost lam L h p)) = 0 := by
    rw [P7fefa2a3.minPoint_eq lam L h p hh hp, hm]
  set c := h * p / (h + p) with hc_def
  have hH := P7fefa2a3.Hd_eq lam L h p hh hp
  have hint : (∫ y in (0 : ℝ)..Q, Hfun (eoqCost lam L h p) y) = c * (Q ^ 2 / 2) := by
    rw [intervalIntegral.integral_congr (g := fun y => c * y)]
    · rw [intervalIntegral.integral_const_mul, integral_id]; ring
    · intro y hy
      rw [Set.uIcc_of_le hQ] at hy
      exact hH y hy.1
  have hint0 : (∫ y in (0 : ℝ)..Q, H0fun (eoqCost lam L h p) y) = c * (Q ^ 2 / 2) := by
    rw [intervalIntegral.integral_congr (g := fun y => c * y)]
    · rw [intervalIntegral.integral_const_mul, integral_id]; ring
    · intro y hy
      rw [Set.uIcc_of_le hQ] at hy
      simp only [H0fun]
      rw [hH y hy.1, hmin, sub_zero]
  have h0Q : H0fun (eoqCost lam L h p) Q = c * Q := by
    unfold H0fun; rw [hH Q hQ, hmin, sub_zero]
  unfold Afun
  rw [hint, hint0, h0Q, hH Q hQ]
  refine ⟨by ring, by ring, by ring, by ring⟩

open MeasureTheory Filter Topology ZhengQR.OrderQty in
theorem solution
    {lam L h p : ℝ} {μ : Measure ℝ}
    (hlam : 0 < lam) (hL : 0 < L) (hh : 0 < h) (hp : 0 < p)
    (hμ : IsLeadtimeDemand lam L μ)
    (hG : ∃! y : ℝ, IsMinimizer (newsvendorCost h p μ) y) :
    (∀ Q : ℝ, 0 ≤ Q →
      1 / 2 * Q * Hfun (newsvendorCost h p μ) Q ≤ ∫ y in (0 : ℝ)..Q, Hfun (newsvendorCost h p μ) y ∧
      Afun (newsvendorCost h p μ) Q ≤ 1 / 2 * Q * Hfun (newsvendorCost h p μ) Q ∧
      1 / 2 * Q * H0fun (newsvendorCost h p μ) Q ≤ Afun (newsvendorCost h p μ) Q ∧
      (∫ y in (0 : ℝ)..Q, H0fun (newsvendorCost h p μ) y) ≤ 1 / 2 * Q * H0fun (newsvendorCost h p μ) Q) ∧
    (∀ Q : ℝ, 0 ≤ Q →
      1 / 2 * Q * Hfun (eoqCost lam L h p) Q = ∫ y in (0 : ℝ)..Q, Hfun (eoqCost lam L h p) y ∧
      Afun (eoqCost lam L h p) Q = 1 / 2 * Q * Hfun (eoqCost lam L h p) Q ∧
      1 / 2 * Q * H0fun (eoqCost lam L h p) Q = Afun (eoqCost lam L h p) Q ∧
      (∫ y in (0 : ℝ)..Q, H0fun (eoqCost lam L h p) y) = 1 / 2 * Q * H0fun (eoqCost lam L h p) Q) := by
  exact ⟨fun Q hQ => stoch_part hlam hL hh hp hμ hG Q hQ, fun Q hQ => det_part hh hp Q hQ⟩

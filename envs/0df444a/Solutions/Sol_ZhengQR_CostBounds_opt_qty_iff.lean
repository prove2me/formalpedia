-- Prove2me | solution 1 for ZhengQR.CostBounds.opt_qty_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:55:49.415377+00:00
-- url     : https://prove2.me/submissions/1c38d696-f7d5-4505-ab80-f246414b2aab

import Mathlib
import Definitions.Def_ZhengQR_CostBounds_QRMachinery
import Definitions.Def_ZhengQR_CostBounds_Model

namespace ZhengQR.CostBounds

open MeasureTheory Filter Topology

lemma aux_oqi_integrable (M : QRModel) (y : ℝ) :
    Integrable (fun x : ℝ => M.h * max (y - x) 0 + M.p * max (x - y) 0) M.μ := by
  have := M.isProb
  have h1 : Integrable (fun x : ℝ => y - x) M.μ := (integrable_const y).sub M.integrable_id
  have h2 : Integrable (fun x : ℝ => x - y) M.μ := M.integrable_id.sub (integrable_const y)
  exact (h1.pos_part.const_mul M.h).add (h2.pos_part.const_mul M.p)

lemma aux_oqi_maxconv (a b u v : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max (a * u + b * v) 0 ≤ a * max u 0 + b * max v 0 := by
  have h1 := mul_le_mul_of_nonneg_left (le_max_left u 0) ha
  have h2 := mul_le_mul_of_nonneg_left (le_max_left v 0) hb
  have h3 := mul_nonneg ha (le_max_right u 0)
  have h4 := mul_nonneg hb (le_max_right v 0)
  exact max_le (by linarith) (by linarith)

lemma aux_oqi_convex (M : QRModel) : ConvexOn ℝ Set.univ M.G := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [QRModel.G, newsvendorCost, smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((aux_oqi_integrable M x).const_mul a) ((aux_oqi_integrable M y).const_mul b)]
  refine integral_mono (aux_oqi_integrable M _)
    (((aux_oqi_integrable M x).const_mul a).add ((aux_oqi_integrable M y).const_mul b))
    (fun ξ => ?_)
  have e1 : a * x + b * y - ξ = a * (x - ξ) + b * (y - ξ) := by
    have : ξ = (a + b) * ξ := by rw [hab, one_mul]
    linarith [this]
  have e2 : ξ - (a * x + b * y) = a * (ξ - x) + b * (ξ - y) := by
    have : ξ = (a + b) * ξ := by rw [hab, one_mul]
    linarith [this]
  have k1 := aux_oqi_maxconv a b (x - ξ) (y - ξ) ha hb
  have k2 := aux_oqi_maxconv a b (ξ - x) (ξ - y) ha hb
  rw [← e1] at k1
  rw [← e2] at k2
  have hh := M.h_pos
  have hp := M.p_pos
  have k1' := mul_le_mul_of_nonneg_left k1 hh.le
  have k2' := mul_le_mul_of_nonneg_left k2 hp.le
  simp only
  nlinarith [k1', k2']

lemma aux_oqi_cont (M : QRModel) : Continuous M.G :=
  continuousOn_univ.mp ((aux_oqi_convex M).continuousOn isOpen_univ)

lemma aux_oqi_lb1 (M : QRModel) (y : ℝ) : M.h * (y - M.lam * M.L) ≤ M.G y := by
  have := M.isProb
  have hi : Integrable (fun x : ℝ => M.h * (y - x)) M.μ :=
    ((integrable_const y).sub M.integrable_id).const_mul _
  have : ∫ x, M.h * (y - x) ∂M.μ = M.h * (y - M.lam * M.L) := by
    rw [integral_const_mul, integral_sub (integrable_const y) M.integrable_id, integral_const,
      M.mean_eq]
    simp
  rw [← this]
  refine integral_mono hi (aux_oqi_integrable M y) (fun x => ?_)
  have h1 := mul_le_mul_of_nonneg_left (le_max_left (y - x) 0) M.h_pos.le
  have h2 := mul_nonneg M.p_pos.le (le_max_right (x - y) 0)
  simp only
  linarith

lemma aux_oqi_lb2 (M : QRModel) (y : ℝ) : M.p * (M.lam * M.L - y) ≤ M.G y := by
  have := M.isProb
  have hi : Integrable (fun x : ℝ => M.p * (x - y)) M.μ :=
    (M.integrable_id.sub (integrable_const y)).const_mul _
  have : ∫ x, M.p * (x - y) ∂M.μ = M.p * (M.lam * M.L - y) := by
    rw [integral_const_mul, integral_sub M.integrable_id (integrable_const y), integral_const,
      M.mean_eq]
    simp
  rw [← this]
  refine integral_mono hi (aux_oqi_integrable M y) (fun x => ?_)
  have h1 := mul_le_mul_of_nonneg_left (le_max_left (x - y) 0) M.p_pos.le
  have h2 := mul_nonneg M.h_pos.le (le_max_right (y - x) 0)
  simp only
  linarith

lemma aux_oqi_deriv (G : ℝ → ℝ) (hG : Continuous G) (Q s : ℝ) :
    HasDerivAt (fun s => ∫ y in s..s + Q, G y) (G (s + Q) - G s) s := by
  have e : (fun s => ∫ y in s..s + Q, G y) =
      fun s => (∫ y in (0 : ℝ)..s + Q, G y) - ∫ y in (0 : ℝ)..s, G y := by
    funext s
    rw [intervalIntegral.integral_interval_sub_left (hG.intervalIntegrable _ _)
      (hG.intervalIntegrable _ _)]
  rw [e]
  have h1 := (hG.integral_hasStrictDerivAt 0 (s + Q)).hasDerivAt
  have h2 := (hG.integral_hasStrictDerivAt 0 s).hasDerivAt
  have h3 : HasDerivAt (fun s : ℝ => s + Q) 1 s := (hasDerivAt_id s).add_const Q
  have h4 := h1.comp s h3
  have h5 := h4.sub h2
  rw [mul_one] at h5
  exact h5

lemma aux_oqi_exists (M : QRModel) (Q : ℝ) (hQ : 0 < Q) :
    ∃ r, ∀ r', (∫ y in r..r + Q, M.G y) ≤ ∫ y in r'..r' + Q, M.G y := by
  have hc := aux_oqi_cont M
  have hΦc : Continuous (fun s => ∫ y in s..s + Q, M.G y) :=
    continuous_iff_continuousAt.2 fun s => (aux_oqi_deriv _ hc Q s).continuousAt
  apply hΦc.exists_forall_le
  rw [cocompact_eq_atBot_atTop, tendsto_sup]
  have hp := M.p_pos
  have hh := M.h_pos
  constructor
  · have ht : Tendsto (fun s : ℝ => Q * M.p * (-s) + Q * M.p * (M.lam * M.L - Q)) atBot atTop :=
      tendsto_atTop_add_const_right _ _
        (tendsto_neg_atBot_atTop.const_mul_atTop (by positivity))
    refine tendsto_atTop_mono (fun s => ?_) ht
    have hm := intervalIntegral.integral_mono_on (μ := volume) (by linarith : s ≤ s + Q)
      (intervalIntegrable_const (c := M.p * (M.lam * M.L - (s + Q))))
      (hc.intervalIntegrable _ _)
      (fun y hy => le_trans (by nlinarith [hy.2]) (aux_oqi_lb2 M y))
    rw [intervalIntegral.integral_const, smul_eq_mul] at hm
    have : s + Q - s = Q := by ring
    rw [this] at hm
    nlinarith [hm]
  · have ht : Tendsto (fun s : ℝ => Q * M.h * s + Q * M.h * (- (M.lam * M.L))) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop (by positivity))
    refine tendsto_atTop_mono (fun s => ?_) ht
    have hm := intervalIntegral.integral_mono_on (μ := volume) (by linarith : s ≤ s + Q)
      (intervalIntegrable_const (c := M.h * (s - M.lam * M.L)))
      (hc.intervalIntegrable _ _)
      (fun y hy => le_trans (by nlinarith [hy.1]) (aux_oqi_lb1 M y))
    rw [intervalIntegral.integral_const, smul_eq_mul] at hm
    have : s + Q - s = Q := by ring
    rw [this] at hm
    nlinarith [hm]

lemma aux_oqi_foc (G : ℝ → ℝ) (hG : Continuous G) (Q r : ℝ)
    (hr : ∀ r', (∫ y in r..r + Q, G y) ≤ ∫ y in r'..r' + Q, G y) : G (r + Q) = G r := by
  have hmin : IsLocalMin (fun s => ∫ y in s..s + Q, G y) r := Filter.Eventually.of_forall hr
  have := hmin.hasDerivAt_eq_zero (aux_oqi_deriv G hG Q r)
  linarith

lemma aux_oqi_opt_iff (G : ℝ → ℝ) (lam K Q r : ℝ) (hQ : 0 < Q) :
    IsOptReorder G lam K Q r ↔ ∀ r', (∫ y in r..r + Q, G y) ≤ ∫ y in r'..r' + Q, G y := by
  unfold IsOptReorder qrCost
  constructor
  · intro h r'
    have := h r'
    rw [div_le_div_iff_of_pos_right hQ] at this
    linarith
  · intro h r'
    rw [div_le_div_iff_of_pos_right hQ]
    linarith [h r']

lemma aux_oqi_reorder (M : QRModel) (Q : ℝ) (hQ : 0 < Q) :
    ∀ r', (∫ y in reorderPt M.G M.lam M.K Q..reorderPt M.G M.lam M.K Q + Q, M.G y) ≤
      ∫ y in r'..r' + Q, M.G y := by
  have hex : ∃ r, IsOptReorder M.G M.lam M.K Q r := by
    obtain ⟨r, hr⟩ := aux_oqi_exists M Q hQ
    exact ⟨r, (aux_oqi_opt_iff _ _ _ _ _ hQ).2 hr⟩
  have : IsOptReorder M.G M.lam M.K Q (reorderPt M.G M.lam M.K Q) := by
    unfold reorderPt
    rw [dif_pos hex]
    exact hex.choose_spec
  exact (aux_oqi_opt_iff _ _ _ _ _ hQ).1 this

lemma aux_oqi_kl (G : ℝ → ℝ) (hc : Continuous G) (hG : ConvexOn ℝ Set.univ G)
    (a b t u v : ℝ) (hab : a < b) (ha : G a = t) (hb : G b = t) (huv : u ≤ v) :
    (∫ y in a..b, G y) - t * (b - a) ≤ (∫ y in u..v, G y) - t * (v - u) := by
  set n : ℝ → ℝ := fun y => max (t - G y) 0 with hn
  have hnc : Continuous n := (continuous_const.sub hc).max continuous_const
  have hn0 : ∀ y, 0 ≤ n y := fun y => le_max_right _ _
  have hle : ∀ y, y ≤ a → n y = 0 := by
    intro y hy
    have : G a ≤ G y := hG.le_left_of_right_le'' (Set.mem_univ _) (Set.mem_univ _) hy hab
      (by rw [ha, hb])
    simp only [hn]
    exact max_eq_right (by linarith)
  have hge : ∀ y, b ≤ y → n y = 0 := by
    intro y hy
    have : G b ≤ G y := hG.le_right_of_left_le'' (Set.mem_univ _) (Set.mem_univ _) hab hy
      (by rw [ha, hb])
    simp only [hn]
    exact max_eq_right (by linarith)
  have hmid : ∀ y ∈ Set.Icc a b, n y = t - G y := by
    intro y hy
    have : G y ≤ max (G a) (G b) := hG.le_on_segment (Set.mem_univ _) (Set.mem_univ _)
      (by rw [segment_eq_Icc hab.le]; exact hy)
    rw [ha, hb, max_self] at this
    simp only [hn]
    exact max_eq_left (by linarith)
  have hsubc : Continuous (fun y => t - G y) := continuous_const.sub hc
  have hI_ab : ∫ y in a..b, n y = t * (b - a) - ∫ y in a..b, G y := by
    rw [intervalIntegral.integral_congr (g := fun y => t - G y)
      (by rw [Set.uIcc_of_le hab.le]; exact hmid)]
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hc.intervalIntegrable _ _),
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hI_uv : t * (v - u) - (∫ y in u..v, G y) ≤ ∫ y in u..v, n y := by
    have h := intervalIntegral.integral_mono_on (μ := volume) (f := fun y => t - G y) (g := n) huv
      (hsubc.intervalIntegrable u v) (hnc.intervalIntegrable u v)
      (fun y _ => le_max_left (t - G y) 0)
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hc.intervalIntegrable _ _),
      intervalIntegral.integral_const, smul_eq_mul] at h
    linarith
  have h3 : ∫ y in u..v, n y ≤ ∫ y in (min u a)..(max v b), n y :=
    intervalIntegral.integral_mono_interval (min_le_left u a) huv (le_max_left v b)
      (Filter.Eventually.of_forall hn0) (hnc.intervalIntegrable _ _)
  have e1 : ∫ y in (min u a)..a, n y = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro y hy
      rw [Set.uIcc_of_le (min_le_right u a)] at hy
      exact hle y hy.2
  have e2 : ∫ y in b..(max v b), n y = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro y hy
      rw [Set.uIcc_of_le (le_max_right v b)] at hy
      exact hge y hy.1
  have s1 := intervalIntegral.integral_add_adjacent_intervals
    (hnc.intervalIntegrable (μ := volume) (min u a) a) (hnc.intervalIntegrable a (max v b))
  have s2 := intervalIntegral.integral_add_adjacent_intervals
    (hnc.intervalIntegrable (μ := volume) a b) (hnc.intervalIntegrable b (max v b))
  linarith

end ZhengQR.CostBounds

open ZhengQR.CostBounds
open MeasureTheory Filter Topology

theorem solution (M : QRModel) (Q : ℝ) (hQ : 0 < Q) :
    IsOptQty M.G M.lam M.K Q ↔ Hfun M.G M.lam M.K Q = Cfun M.G M.lam M.K Q := by
  have hc := aux_oqi_cont M
  have hropt := aux_oqi_reorder M Q hQ
  set r := reorderPt M.G M.lam M.K Q with hr_def
  have hH : Hfun M.G M.lam M.K Q = M.G r := by
    unfold Hfun
    rw [if_pos hQ]
  have hC : Cfun M.G M.lam M.K Q = (M.lam * M.K + ∫ y in r..r + Q, M.G y) / Q := rfl
  have hCle : ∀ Q', 0 < Q' → ∀ r',
      Cfun M.G M.lam M.K Q' ≤ (M.lam * M.K + ∫ y in r'..r' + Q', M.G y) / Q' := by
    intro Q' hQ' r'
    unfold Cfun qrCost
    rw [div_le_div_iff_of_pos_right hQ']
    linarith [aux_oqi_reorder M Q' hQ' r']
  rw [hH]
  set I := ∫ y in r..r + Q, M.G y with hI
  set c := (M.lam * M.K + I) / Q with hc_def
  have hcQ : c * Q = M.lam * M.K + I := div_mul_cancel₀ _ hQ.ne'
  rw [hC]
  constructor
  · rintro ⟨_, hopt⟩
    rcases lt_trichotomy (M.G r) c with hlt | heq | hgt
    · exfalso
      set c' := (M.G r + c) / 2 with hc'
      have hev : ∀ᶠ z in 𝓝 r, M.G z < c' :=
        hc.continuousAt.eventually_lt continuousAt_const (by rw [hc']; linarith)
      obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
      set ε := δ / 2 with hε_def
      have hε : 0 < ε := by positivity
      have hbound : ∫ y in (r - ε)..r, M.G y ≤ ε * c' := by
        have hm := intervalIntegral.integral_mono_on (μ := volume) (by linarith : r - ε ≤ r)
          (hc.intervalIntegrable _ _) (intervalIntegrable_const (c := c'))
          (fun z hz => (hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hz.1, hz.2])).le)
        rw [intervalIntegral.integral_const, smul_eq_mul] at hm
        have : r - (r - ε) = ε := by ring
        rw [this] at hm
        exact hm
      have hsplit : ∫ y in (r - ε)..(r - ε + (Q + ε)), M.G y = (∫ y in (r - ε)..r, M.G y) + I := by
        rw [show r - ε + (Q + ε) = r + Q by ring]
        exact (intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
          (hc.intervalIntegrable _ _)).symm
      have h1 := hCle (Q + ε) (by linarith) (r - ε)
      have h2 := hopt (Q + ε) (by linarith)
      have h3 : (M.lam * M.K + ∫ y in (r - ε)..(r - ε + (Q + ε)), M.G y) / (Q + ε) < c := by
        rw [div_lt_iff₀ (by linarith), hsplit]
        have : ε * c' < ε * c := mul_lt_mul_of_pos_left (by rw [hc']; linarith) hε
        nlinarith
      rw [hC] at h2
      linarith
    · exact heq
    · exfalso
      set c' := (M.G r + c) / 2 with hc'
      have hev : ∀ᶠ z in 𝓝 r, c' < M.G z :=
        continuousAt_const.eventually_lt hc.continuousAt (by rw [hc']; linarith)
      obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
      set ε := min (δ / 2) (Q / 2) with hε_def
      have hε : 0 < ε := lt_min (by positivity) (by positivity)
      have hεδ : ε ≤ δ / 2 := min_le_left _ _
      have hεQ : ε ≤ Q / 2 := min_le_right _ _
      have hbound : ε * c' ≤ ∫ y in r..(r + ε), M.G y := by
        have hm := intervalIntegral.integral_mono_on (μ := volume) (by linarith : r ≤ r + ε)
          (intervalIntegrable_const (c := c')) (hc.intervalIntegrable _ _)
          (fun z hz => (hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hz.1, hz.2])).le)
        rw [intervalIntegral.integral_const, smul_eq_mul] at hm
        have : r + ε - r = ε := by ring
        rw [this] at hm
        exact hm
      have hsplit : I = (∫ y in r..(r + ε), M.G y) + ∫ y in (r + ε)..(r + ε + (Q - ε)), M.G y := by
        rw [show r + ε + (Q - ε) = r + Q by ring]
        exact (intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
          (hc.intervalIntegrable _ _)).symm
      have h1 := hCle (Q - ε) (by linarith) (r + ε)
      have h2 := hopt (Q - ε) (by linarith)
      have h3 : (M.lam * M.K + ∫ y in (r + ε)..(r + ε + (Q - ε)), M.G y) / (Q - ε) < c := by
        rw [div_lt_iff₀ (by linarith)]
        have : ε * c < ε * c' := mul_lt_mul_of_pos_left (by rw [hc']; linarith) hε
        nlinarith
      rw [hC] at h2
      linarith
  · intro heq
    refine ⟨hQ, fun Q' hQ' => ?_⟩
    have hfoc := aux_oqi_foc M.G hc Q r hropt
    rw [hC]
    show c ≤ qrCost M.G M.lam M.K Q' (reorderPt M.G M.lam M.K Q')
    unfold qrCost
    rw [le_div_iff₀ hQ']
    have hkl := aux_oqi_kl M.G hc (aux_oqi_convex M) r (r + Q) c (reorderPt M.G M.lam M.K Q')
      (reorderPt M.G M.lam M.K Q' + Q') (by linarith) heq (hfoc.trans heq) (by linarith)
    have e1 : c * (r + Q - r) = c * Q := by ring
    have e2 : c * (reorderPt M.G M.lam M.K Q' + Q' - reorderPt M.G M.lam M.K Q') = c * Q' := by
      ring
    rw [e1, e2] at hkl
    linarith

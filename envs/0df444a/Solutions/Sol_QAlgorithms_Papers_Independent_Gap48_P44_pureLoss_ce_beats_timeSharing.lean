-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P44.pureLoss_ce_beats_timeSharing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:40:13.37711+00:00
-- url     : https://prove2.me/submissions/c088ffc5-6710-4653-98ba-ebdc28d065c8

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P44
noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P44
open Filter

open scoped ENNReal Topology

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

theorem g78b_gte {x : ℝ} (hx : 0 < x) :
    g x = Real.log (x + 1) + x * Real.log (1 + 1 / x) := by
  unfold g
  have h : Real.log (1 + 1 / x) = Real.log (x + 1) - Real.log x := by
    rw [show (1:ℝ) + 1 / x = (x + 1) / x by field_simp,
      Real.log_div (by positivity) hx.ne']
  rw [h]; ring

theorem g78b_lim (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun G : ℝ => g (a * G) - g (b * G)) atTop
      (nhds (Real.log a - Real.log b)) := by
  have t1 : Tendsto (fun G : ℝ => a * G) atTop atTop := tendsto_id.const_mul_atTop ha
  have t2 : Tendsto (fun G : ℝ => b * G) atTop atTop := tendsto_id.const_mul_atTop hb
  have hA1 := (Real.tendsto_mul_log_one_add_div_atTop 1).comp t1
  have hA2 := (Real.tendsto_mul_log_one_add_div_atTop 1).comp t2
  have hinv := tendsto_inv_atTop_zero (𝕜 := ℝ)
  have hq : Tendsto (fun G : ℝ => (a + G⁻¹) / (b + G⁻¹)) atTop
      (nhds ((a + 0) / (b + 0))) :=
    (tendsto_const_nhds.add hinv).div (tendsto_const_nhds.add hinv) (by simp; linarith)
  have hlog := hq.log (by simp; exact ⟨ha.ne', hb.ne'⟩)
  have hF := (hlog.add hA1).sub hA2
  have hlim : Real.log ((a + 0) / (b + 0)) + 1 - 1 = Real.log a - Real.log b := by
    simp [Real.log_div ha.ne' hb.ne']
  rw [hlim] at hF
  refine hF.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with G hG
  have h1 : 0 < a * G := by positivity
  have h2 : 0 < b * G := by positivity
  simp only [Function.comp]
  rw [g78b_gte h1, g78b_gte h2]
  have hG' : G ≠ 0 := hG.ne'
  have e : (a + G⁻¹) / (b + G⁻¹) = (a * G + 1) / (b * G + 1) := by
    rw [show a + G⁻¹ = (a * G + 1) / G by field_simp,
      show b + G⁻¹ = (b * G + 1) / G by field_simp,
      div_div_div_cancel_right₀ hG']
  rw [e, Real.log_div (by linarith) (by linarith)]
  ring

theorem g78b_ge_log {v : ℝ} (hv : 0 ≤ v) : Real.log (v + 1) ≤ g v := by
  unfold g
  have hl : Real.log v ≤ Real.log (v + 1) := by
    rcases hv.eq_or_lt with h | h
    · subst h; simp
    · exact Real.log_le_log h (by linarith)
  nlinarith

theorem g78b_atTop (a : ℝ) (ha : 0 < a) : Tendsto (fun G : ℝ => g (a * G)) atTop atTop := by
  have t1 : Tendsto (fun G : ℝ => a * G) atTop atTop := tendsto_id.const_mul_atTop ha
  have hl : Tendsto (fun G : ℝ => Real.log (a * G + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 1 t1)
  refine tendsto_atTop_mono' _ ?_ hl
  filter_upwards [eventually_gt_atTop (0:ℝ)] with G hG
  exact g78b_ge_log (by positivity)
theorem g78b_two_log_le {y : ℝ} (hy : 1 ≤ y) : 2 * Real.log y ≤ y - 1 / y := by
  let ψ : ℝ → ℝ := fun t => t - t⁻¹ - 2 * Real.log t
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt ψ (1 - (-(x ^ 2)⁻¹) - 2 * x⁻¹) x := by
    intro x hx0
    have := ((hasDerivAt_id' x).sub (hasDerivAt_inv hx0.ne')).sub
      ((Real.hasDerivAt_log hx0.ne').const_mul 2)
    exact this
  have hmono : MonotoneOn ψ (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · intro x hx
      have : (1:ℝ) ≤ x := hx
      exact (hd x (by linarith)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have : (1:ℝ) < x := hx
      exact (hd x (by linarith)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have : (1:ℝ) < x := hx
      rw [(hd x (by linarith)).deriv]
      have : 1 - (-(x ^ 2)⁻¹) - 2 * x⁻¹ = (1 - x⁻¹) ^ 2 := by field_simp; ring
      rw [this]; positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy) hy
  simp only [ψ, inv_one, Real.log_one] at this
  rw [one_div]
  linarith

theorem g78b_g_hasDeriv {v : ℝ} (hv : 0 < v) :
    HasDerivAt g (Real.log (v + 1) - Real.log v) v := by
  have h1 : HasDerivAt (fun v : ℝ => v + 1) 1 v := (hasDerivAt_id v).add_const 1
  have h2 := h1.mul (h1.log (by linarith))
  have h3 := (hasDerivAt_id v).mul (Real.hasDerivAt_log hv.ne')
  have := h2.sub h3
  refine this.congr_deriv ?_
  simp only [id, one_mul]
  field_simp
  ring

/-- u = log(x+1) - log x bounds -/
theorem g78b_u_bounds {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ≤ Real.log (x + 1) - Real.log x ∧
    Real.log (x + 1) - Real.log x ≤ 1 / x ∧
    2 * (Real.log (x + 1) - Real.log x) ≤ 1 / x + 1 / (x + 1) := by
  have hy : 0 < (x + 1) / x := by positivity
  have e : Real.log (x + 1) - Real.log x = Real.log ((x + 1) / x) := by
    rw [Real.log_div (by linarith) hx.ne']
  rw [e]
  refine ⟨?_, ?_, ?_⟩
  · have := Real.one_sub_inv_le_log_of_pos hy
    have h2 : 1 - ((x + 1) / x)⁻¹ = 1 / (x + 1) := by field_simp; ring
    linarith
  · have := Real.log_le_sub_one_of_pos hy
    have h2 : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    linarith
  · have := g78b_two_log_le (y := (x + 1) / x) (by rw [le_div_iff₀ hx]; linarith)
    have h2 : (x + 1) / x - 1 / ((x + 1) / x) = 1 / x + 1 / (x + 1) := by field_simp; ring
    linarith

theorem g78b_g_eq {x : ℝ} (hx : 0 < x) :
    g x = Real.log x + (x + 1) * (Real.log (x + 1) - Real.log x) := by
  unfold g; ring

theorem g78b_hh_ge {x : ℝ} (hx : 0 < x) : 1 ≤ (x + 1) * (Real.log (x + 1) - Real.log x) := by
  have := (g78b_u_bounds hx).1
  have h : (x + 1) * (1 / (x + 1)) = 1 := by field_simp
  nlinarith

theorem g78b_hh_le {x : ℝ} (hx : 0 < x) :
    (x + 1) * (Real.log (x + 1) - Real.log x) ≤ 1 + 1 / x := by
  have := (g78b_u_bounds hx).2.1
  have h : (x + 1) * (1 / x) = 1 + 1 / x := by field_simp
  nlinarith

theorem g78b_hh_le2 {x : ℝ} (hx : 0 < x) :
    (x + 1) * (Real.log (x + 1) - Real.log x) ≤ 1 + 1 / (2 * x) := by
  have := (g78b_u_bounds hx).2.2
  have h : (x + 1) * (1 / x + 1 / (x + 1)) = 2 * (1 + 1 / (2 * x)) := by field_simp; ring
  nlinarith

theorem g78b_hh_anti : AntitoneOn (fun x : ℝ => (x + 1) * (Real.log (x + 1) - Real.log x))
    (Set.Ioi 0) := by
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt (fun x : ℝ => (x + 1) * (Real.log (x + 1) - Real.log x))
      (1 * (Real.log (x + 1) - Real.log x) + (x + 1) * (1 / (x + 1) * 1 - 1 / x)) x := by
    intro x hx
    have h1 : HasDerivAt (fun v : ℝ => v + 1) 1 x := (hasDerivAt_id x).add_const 1
    have h3 : HasDerivAt (fun y : ℝ => Real.log y) x⁻¹ x := Real.hasDerivAt_log hx.ne'
    have h2 := (h1.log (by linarith)).sub h3
    have := h1.mul h2
    refine (this.congr_deriv ?_)
    simp [one_div]
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; intro x hx; exact (hd x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]; intro x hx
    have hx' : 0 < x := hx
    rw [(hd x hx').deriv]
    have := (g78b_u_bounds hx').2.1
    have h : (x + 1) * (1 / (x + 1) * 1 - 1 / x) = - (1 / x) := by field_simp; ring
    rw [h]; linarith

theorem g78b_key {x l : ℝ} (hx : 0 < x) (hl0 : 0 < l) (hl1 : l ≤ 1) :
    l * (Real.log (l * x + 1) - Real.log (l * x)) ≤ Real.log (x + 1) - Real.log x := by
  have hp : 0 < (l * x + 1) / (l * x) := by positivity
  have hg := Real.geom_mean_le_arith_mean2_weighted hl0.le (by linarith : (0:ℝ) ≤ 1 - l)
    hp.le zero_le_one (by ring)
  rw [Real.one_rpow, mul_one] at hg
  have hr : l * ((l * x + 1) / (l * x)) + (1 - l) * 1 = (x + 1) / x := by
    field_simp; ring
  rw [hr] at hg
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hp l) hg
  rw [Real.log_rpow hp, Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) hx.ne'] at hlog
  exact hlog

theorem g78b_phi_mono {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    MonotoneOn (fun x : ℝ => g x - g (c * x)) (Set.Ioi 0) := by
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt (fun x : ℝ => g x - g (c * x))
      ((Real.log (x + 1) - Real.log x) -
        (Real.log (c * x + 1) - Real.log (c * x)) * (c * 1)) x := by
    intro x hx
    exact (g78b_g_hasDeriv hx).sub ((g78b_g_hasDeriv (mul_pos hc0 hx)).comp x
      ((hasDerivAt_id x).const_mul c))
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; intro x hx; exact (hd x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]; intro x hx
    have hx' : 0 < x := hx
    rw [(hd x hx').deriv]
    have := g78b_key hx' hc0 hc1
    nlinarith
theorem g78b_L_pos {z : ℝ} (hz : 0 < z) : 0 < Real.log (z + 1) - Real.log z := by
  have := Real.log_lt_log hz (by linarith : z < z + 1); linarith

theorem g78b_L_hasDeriv {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z : ℝ => Real.log (z + 1) - Real.log z) (1 / (z + 1) - 1 / z) z := by
  have h1 : HasDerivAt (fun v : ℝ => v + 1) 1 z := (hasDerivAt_id z).add_const 1
  have h3 : HasDerivAt (fun y : ℝ => Real.log y) z⁻¹ z := Real.hasDerivAt_log hz.ne'
  have := (h1.log (by linarith)).sub h3
  refine this.congr_deriv ?_
  simp [one_div]

theorem g78b_hh_santi : StrictAntiOn (fun x : ℝ => (x + 1) * (Real.log (x + 1) - Real.log x))
    (Set.Ioi 0) := by
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt (fun x : ℝ => (x + 1) * (Real.log (x + 1) - Real.log x))
      (1 * (Real.log (x + 1) - Real.log x) + (x + 1) * (1 / (x + 1) - 1 / x)) x := by
    intro x hx
    have h1 : HasDerivAt (fun v : ℝ => v + 1) 1 x := (hasDerivAt_id x).add_const 1
    exact h1.mul (g78b_L_hasDeriv hx)
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; intro x hx
    have hx' : 0 < x := hx
    rw [(hd x hx').deriv]
    have hy : 0 < (x + 1) / x := by positivity
    have hne : (x + 1) / x ≠ 1 := by
      intro h; rw [div_eq_one_iff_eq hx'.ne'] at h; linarith
    have hl := Real.log_lt_sub_one_of_pos hy hne
    rw [Real.log_div (by linarith) hx'.ne'] at hl
    have h2 : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    have h : (x + 1) * (1 / (x + 1) - 1 / x) = - (1 / x) := by field_simp; ring
    rw [h]; linarith

/-- L(sx)/L(x) strictly increasing -/
theorem g78b_Lratio {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    StrictMonoOn (fun x : ℝ => (Real.log (s * x + 1) - Real.log (s * x)) /
      (Real.log (x + 1) - Real.log x)) (Set.Ioi 0) := by
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt (fun x : ℝ => (Real.log (s * x + 1) - Real.log (s * x)) /
      (Real.log (x + 1) - Real.log x))
      (((1 / (s * x + 1) - 1 / (s * x)) * (s * 1) * (Real.log (x + 1) - Real.log x) -
        (Real.log (s * x + 1) - Real.log (s * x)) * (1 / (x + 1) - 1 / x)) /
        (Real.log (x + 1) - Real.log x) ^ 2) x := by
    intro x hx
    have a := (g78b_L_hasDeriv (mul_pos hs0 hx)).comp x ((hasDerivAt_id x).const_mul s)
    exact a.div (g78b_L_hasDeriv hx) (g78b_L_pos hx).ne'
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; intro x hx
    have hx' : 0 < x := hx
    rw [(hd x hx').deriv]
    apply div_pos _ (pow_pos (g78b_L_pos hx') 2)
    have hsx : 0 < s * x := mul_pos hs0 hx'
    have A := g78b_hh_santi hsx hx' (by nlinarith)
    simp only at A
    have e : (1 / (s * x + 1) - 1 / (s * x)) * (s * 1) * (Real.log (x + 1) - Real.log x) -
        (Real.log (s * x + 1) - Real.log (s * x)) * (1 / (x + 1) - 1 / x) =
        ((s * x + 1) * (Real.log (s * x + 1) - Real.log (s * x)) -
          (x + 1) * (Real.log (x + 1) - Real.log x)) / (x * (x + 1) * (s * x + 1)) := by
      field_simp; ring
    rw [e]; apply div_pos (by linarith); positivity

theorem g78b_g_cont : Continuous g := by
  unfold g
  exact (Real.continuous_mul_log.comp (continuous_add_right 1)).sub Real.continuous_mul_log

theorem g78b_g_pos {x : ℝ} (hx : 0 < x) : 0 < g x := by
  have := g78b_ge_log hx.le
  have := Real.log_pos (by linarith : (1:ℝ) < x + 1)
  linarith

/-- key: g(sx) L(x) < s L(sx) g(x) -/
theorem g78b_K {s x : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hx : 0 < x) :
    g (s * x) * (Real.log (x + 1) - Real.log x) <
      s * (Real.log (s * x + 1) - Real.log (s * x)) * g x := by
  obtain ⟨c, hc, hE⟩ := exists_ratio_hasDerivAt_eq_ratio_slope (fun y => g (s * y))
    (fun y => (Real.log (s * y + 1) - Real.log (s * y)) * (s * 1)) hx
    ((g78b_g_cont.comp (continuous_const.mul continuous_id)).continuousOn)
    (fun y hy => (g78b_g_hasDeriv (mul_pos hs0 hy.1)).comp y ((hasDerivAt_id y).const_mul s))
    g (fun y => Real.log (y + 1) - Real.log y) g78b_g_cont.continuousOn
    (fun y hy => g78b_g_hasDeriv hy.1)
  have g0 : g 0 = 0 := by simp [g]
  simp only [mul_zero, g0, sub_zero] at hE
  have hc0 : 0 < c := hc.1
  have hR := g78b_Lratio hs0 hs1 hc0 hx hc.2
  simp only at hR
  have L1 := g78b_L_pos hc0
  have L2 := g78b_L_pos hx
  have L3 := g78b_L_pos (mul_pos hs0 hc0)
  have L4 := g78b_L_pos (mul_pos hs0 hx)
  rw [div_lt_div_iff₀ L1 L2] at hR
  have gx := g78b_g_pos hx
  -- hE : g x * (L(sc) * s) = g(sx) * L(c)
  have : g (s * x) * (Real.log (c + 1) - Real.log c) * (Real.log (x + 1) - Real.log x) <
      s * (Real.log (s * x + 1) - Real.log (s * x)) * g x * (Real.log (c + 1) - Real.log c) := by
    rw [← hE]; nlinarith [mul_pos gx hs0]
  nlinarith

theorem g78b_R {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    StrictMonoOn (fun x : ℝ => g (s * x) / g x) (Set.Ioi 0) := by
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt (fun x : ℝ => g (s * x) / g x)
      (((Real.log (s * x + 1) - Real.log (s * x)) * (s * 1) * g x -
        g (s * x) * (Real.log (x + 1) - Real.log x)) / (g x) ^ 2) x := by
    intro x hx
    have a := (g78b_g_hasDeriv (mul_pos hs0 hx)).comp x ((hasDerivAt_id x).const_mul s)
    exact a.div (g78b_g_hasDeriv hx) (g78b_g_pos hx).ne'
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; intro x hx
    have hx' : 0 < x := hx
    rw [(hd x hx').deriv]
    apply div_pos _ (pow_pos (g78b_g_pos hx') 2)
    have := g78b_K hs0 hs1 hx'
    nlinarith

/-- final ratio comparison, multiplied out -/
theorem g78b_cmp {s x y : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hx : 0 < x) (hxy : x < y) :
    g (s * x) * g y < g (s * y) * g x := by
  have := g78b_R hs0 hs1 hx (lt_trans hx hxy) hxy
  simp only at this
  rwa [div_lt_div_iff₀ (g78b_g_pos hx) (g78b_g_pos (lt_trans hx hxy))] at this

theorem g78b_cmp_le {s x y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hx : 0 < x) (hxy : x ≤ y) :
    g (s * x) * g y ≤ g (s * y) * g x := by
  rcases hs0.eq_or_lt with h | h
  · subst h; simp [g]
  rcases hs1.eq_or_lt with h' | h'
  · subst h'; simp; ring_nf; rfl
  rcases hxy.eq_or_lt with h'' | h''
  · subst h''; rfl
  exact (g78b_cmp h h' hx h'').le
theorem g78b_g_mono : MonotoneOn g (Set.Ici 0) := by
  have hc : ContinuousOn g (Set.Ici 0) := by
    have h1 : ContinuousOn (fun v : ℝ => (v + 1) * Real.log (v + 1)) (Set.Ici 0) := by
      apply ContinuousOn.mul (continuousOn_id.add continuousOn_const)
      apply ContinuousOn.log (continuousOn_id.add continuousOn_const)
      intro x hx; have : (0:ℝ) ≤ x := hx; exact ne_of_gt (by simp; linarith)
    exact h1.sub Real.continuous_mul_log.continuousOn
  have hd : ∀ v : ℝ, 0 < v → HasDerivAt g (Real.log (v + 1) - Real.log v) v := by
    intro v hv
    have h1 : HasDerivAt (fun v : ℝ => v + 1) 1 v := (hasDerivAt_id v).add_const 1
    have h2 := h1.mul (h1.log (by linarith))
    have h3 := (hasDerivAt_id v).mul (Real.hasDerivAt_log hv.ne')
    have := h2.sub h3
    refine this.congr_deriv ?_
    simp only [id, one_mul]
    field_simp
    ring
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hc
  · rw [interior_Ici]; intro x hx; exact (hd x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]; intro x hx
    have hx' : (0:ℝ) < x := hx
    rw [(hd x hx').deriv]
    have := Real.log_le_log hx' (by linarith : x ≤ x + 1)
    linarith

theorem g78b_te_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : thermalEntropy x ≤ thermalEntropy y := by
  have := g78b_g_mono hx (le_trans hx hxy : (0:ℝ) ≤ y) hxy
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  show g x / Real.log 2 ≤ g y / Real.log 2
  exact div_le_div_of_nonneg_right this hl2.le


/-- PDF pp.7-8, Figure 2(b): proper CE-family inclusion at the caption's budget.
The second coordinate is nonnegative entanglement CONSUMPTION. -/
theorem solution (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta < 1) :
    let budget := 50 / (1 - eta)
    ceTimeSharing (thermalEntropy (eta * budget))
      (thermalEntropy budget + thermalEntropy (eta * budget) -
        thermalEntropy ((1 - eta) * budget)) (thermalEntropy budget) ⊂
      lossCE eta budget := by
  intro budget
  have h0 : 0 < 1 - eta := by linarith
  have hB : 0 < budget := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hte : ∀ x, thermalEntropy x = g x / Real.log 2 := fun x => rfl
  have hcd : (1 - eta) * budget < budget := by nlinarith
  have hcB : 0 < (1 - eta) * budget := by positivity
  have hdB : 0 < eta * budget := by positivity
  have gc := g78b_g_pos hcB
  have gB := g78b_g_pos hB
  have gd := g78b_g_pos hdB
  have e2 : ∀ s : ℝ, (1 - eta) * s * budget = s * ((1 - eta) * budget) := fun s => by ring
  have hsub : ceTimeSharing (thermalEntropy (eta * budget))
      (thermalEntropy budget + thermalEntropy (eta * budget) -
        thermalEntropy ((1 - eta) * budget)) (thermalEntropy budget) ⊆
        lossCE eta budget := by
    rintro r ⟨hr1, hr2, t, ⟨ht0, ht1⟩, h1, h2⟩
    have hf : ContinuousOn (fun s : ℝ => g (s * ((1 - eta) * budget))) (Set.Icc 0 1) :=
      (g78b_g_cont.comp (continuous_id.mul continuous_const)).continuousOn
    have hmem : t * g ((1 - eta) * budget) ∈ Set.Icc (g (0 * ((1 - eta) * budget)))
        (g (1 * ((1 - eta) * budget))) := by
      simp only [zero_mul, one_mul]
      refine ⟨?_, ?_⟩
      · simp [g]; positivity
      · nlinarith
    obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ := intermediate_value_Icc zero_le_one hf hmem
    simp only at hs
    have hcmp := g78b_cmp_le hs0 hs1 hcB hcd.le
    have ht : t * g budget ≤ g (s * budget) := by
      rw [hs] at hcmp
      have : t * g budget * g ((1 - eta) * budget) ≤
          g (s * budget) * g ((1 - eta) * budget) := by nlinarith
      exact le_of_mul_le_mul_right this gc
    have h1' : r.1 * Real.log 2 ≤ g (eta * budget) + t * g budget - t * g ((1 - eta) * budget) := by
      have := mul_le_mul_of_nonneg_right h1 hl2.le
      rw [hte, hte, hte, show ((1 - t) * (g (eta * budget) / Real.log 2) + t * (g budget / Real.log 2
        + g (eta * budget) / Real.log 2 - g ((1 - eta) * budget) / Real.log 2)) * Real.log 2
        = g (eta * budget) + t * g budget - t * g ((1 - eta) * budget) by field_simp; ring] at this
      exact this
    have h2' : t * g budget ≤ r.2 * Real.log 2 := by
      have := mul_le_mul_of_nonneg_right h2 hl2.le
      rw [hte, show t * (g budget / Real.log 2) * Real.log 2 = t * g budget by field_simp] at this
      exact this
    refine ⟨hr1, hr2, s, ⟨hs0, hs1⟩, ?_, ?_⟩
    · simp only
      rw [e2, hte, hte, hte, show g (s * budget) / Real.log 2 + g (eta * budget) / Real.log 2 -
        g (s * ((1 - eta) * budget)) / Real.log 2 = (g (s * budget) + g (eta * budget) -
        g (s * ((1 - eta) * budget))) / Real.log 2 by ring, le_div_iff₀ hl2, hs]
      nlinarith
    · simp only
      rw [e2, hte, hte, show g (eta * budget) / Real.log 2 -
        g (s * ((1 - eta) * budget)) / Real.log 2 + r.2 = (g (eta * budget) -
        g (s * ((1 - eta) * budget)) + r.2 * Real.log 2) / Real.log 2 by field_simp,
        le_div_iff₀ hl2, hs]
      nlinarith
  refine (Set.ssubset_iff_of_subset hsub).2 ?_
  have hA := g78b_g_mono (Set.mem_Ici.2 (by positivity : (0:ℝ) ≤ (1/2) * ((1 - eta) * budget)))
    (Set.mem_Ici.2 (by positivity : (0:ℝ) ≤ (1/2) * budget))
    (by nlinarith : (1/2) * ((1 - eta) * budget) ≤ (1/2) * budget)
  have hA2 := g78b_g_pos (by positivity : (0:ℝ) < (1/2) * budget)
  have hgg : 0 ≤ g budget - g ((1 - eta) * budget) := by
    have := g78b_g_mono (Set.mem_Ici.2 hcB.le) (Set.mem_Ici.2 hB.le) hcd.le; linarith
  have hcmp := g78b_cmp (by norm_num : (0:ℝ) < 1/2) (by norm_num) hcB hcd
  refine ⟨((g ((1/2) * budget) + g (eta * budget) - g ((1/2) * ((1 - eta) * budget))) / Real.log 2,
    g ((1/2) * budget) / Real.log 2), ?_, ?_⟩
  · refine ⟨div_nonneg (by linarith) hl2.le, div_nonneg (by linarith) hl2.le, 1/2,
      ⟨by norm_num, by norm_num⟩, ?_, ?_⟩
    · simp only; rw [e2, hte, hte, hte]; apply le_of_eq; ring
    · simp only; rw [e2, hte, hte]; apply le_of_eq; ring
  · rintro ⟨_, _, t, ⟨ht0, ht1⟩, h1, h2⟩
    simp only at h1 h2
    have h1' : g ((1/2) * budget) + g (eta * budget) - g ((1/2) * ((1 - eta) * budget)) ≤
        g (eta * budget) + t * g budget - t * g ((1 - eta) * budget) := by
      have := mul_le_mul_of_nonneg_right h1 hl2.le
      rw [hte, hte, hte, show ((1 - t) * (g (eta * budget) / Real.log 2) + t * (g budget / Real.log 2
        + g (eta * budget) / Real.log 2 - g ((1 - eta) * budget) / Real.log 2)) * Real.log 2
        = g (eta * budget) + t * g budget - t * g ((1 - eta) * budget) by field_simp; ring,
        div_mul_cancel₀ _ hl2.ne'] at this
      exact this
    have h2' : t * g budget ≤ g ((1/2) * budget) := by
      have := mul_le_mul_of_nonneg_right h2 hl2.le
      rw [hte, show t * (g budget / Real.log 2) * Real.log 2 = t * g budget by field_simp,
        div_mul_cancel₀ _ hl2.ne'] at this
      exact this
    have k1 : (g ((1/2) * budget) - g ((1/2) * ((1 - eta) * budget))) * g budget ≤
        t * (g budget - g ((1 - eta) * budget)) * g budget :=
      mul_le_mul_of_nonneg_right (by linarith) gB.le
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ g ((1/2) * budget) - t * g budget) hgg]


end

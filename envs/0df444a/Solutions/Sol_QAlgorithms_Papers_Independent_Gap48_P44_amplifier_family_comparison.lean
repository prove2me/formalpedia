-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P44.amplifier_family_comparison
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:58:49.472341+00:00
-- url     : https://prove2.me/submissions/f27764c2-2f36-4968-b968-1bc9008fa4aa

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

theorem g78b_Lf_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.log (y + 1) - Real.log y ≤ Real.log (x + 1) - Real.log x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  rw [← Real.log_div (by linarith) hx.ne', ← Real.log_div (by linarith) hy.ne']
  apply Real.log_le_log (by positivity)
  rw [div_le_div_iff₀ hy hx]; nlinarith

theorem g78b_Lf_lower {z : ℝ} (hz : 0 < z) : 2 / (2 * z + 1) ≤ Real.log (z + 1) - Real.log z := by
  let ψ : ℝ → ℝ := fun y => Real.log y - 2 * (y - 1) / (y + 1)
  have hd : ∀ y : ℝ, 0 < y → HasDerivAt ψ (y⁻¹ - ((2 * 1) * (y + 1) - 2 * (y - 1) * 1) / (y + 1) ^ 2) y := by
    intro y hy
    have h1 : HasDerivAt (fun y : ℝ => 2 * (y - 1)) (2 * 1) y := ((hasDerivAt_id y).sub_const 1).const_mul 2
    have h2 : HasDerivAt (fun y : ℝ => y + 1) 1 y := (hasDerivAt_id y).add_const 1
    exact (Real.hasDerivAt_log hy.ne').sub (h1.div h2 (by linarith))
  have hmono : MonotoneOn ψ (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · intro x hx
      have : (1:ℝ) ≤ x := hx
      exact (hd x (by linarith)).continuousAt.continuousWithinAt
    · rw [interior_Ici]; intro x hx
      have : (1:ℝ) < x := hx
      exact (hd x (by linarith)).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]; intro x hx
      have : (1:ℝ) < x := hx
      rw [(hd x (by linarith)).deriv]
      have e : x⁻¹ - ((2 * 1) * (x + 1) - 2 * (x - 1) * 1) / (x + 1) ^ 2 = (x - 1) ^ 2 / (x * (x + 1) ^ 2) := by
        field_simp; ring
      rw [e]; positivity
  have hy1 : (1:ℝ) ≤ (z + 1) / z := by rw [le_div_iff₀ hz]; linarith
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy1) hy1
  simp only [ψ, Real.log_one] at this
  rw [Real.log_div (by linarith) hz.ne'] at this
  have e2 : 2 * ((z + 1) / z - 1) / ((z + 1) / z + 1) = 2 / (2 * z + 1) := by field_simp; ring
  rw [e2] at this
  norm_num at this
  linarith

theorem g78b_Lf_upper {x : ℝ} (hx : 0 < x) :
    Real.log (x + 1) - Real.log x ≤ (2 * x + 1) / (2 * x * (x + 1)) := by
  have := (g78b_u_bounds hx).2.2
  have e : (2 * x + 1) / (2 * x * (x + 1)) = (1 / x + 1 / (x + 1)) / 2 := by field_simp; ring
  rw [e]; linarith

/-- monotone l'Hopital rule -/
theorem g78b_lhop {F G F' G' : ℝ → ℝ} {x0 : ℝ} (hF0 : F x0 = 0) (hG0 : G x0 = 0)
    (hFc : Continuous F) (hGc : Continuous G)
    (hFd : ∀ x, x0 < x → HasDerivAt F (F' x) x) (hGd : ∀ x, x0 < x → HasDerivAt G (G' x) x)
    (hG'pos : ∀ x, x0 < x → 0 < G' x)
    (hanti : StrictAntiOn (fun x => F' x / G' x) (Set.Ioi x0)) :
    StrictAntiOn (fun x => F x / G x) (Set.Ioi x0) := by
  have hGmono : StrictMonoOn G (Set.Ici x0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici x0) hGc.continuousOn
    rw [interior_Ici]; intro x hx
    rw [(hGd x hx).deriv]; exact hG'pos x hx
  have hGpos : ∀ x, x0 < x → 0 < G x := by
    intro x hx
    have := hGmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx.le) hx
    rwa [hG0] at this
  have hd : ∀ x, x0 < x → HasDerivAt (fun x => F x / G x)
      ((F' x * G x - F x * G' x) / (G x) ^ 2) x :=
    fun x hx => (hFd x hx).div (hGd x hx) (hGpos x hx).ne'
  apply strictAntiOn_of_deriv_neg (convex_Ioi x0)
  · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; intro x hx
    have hx' : x0 < x := hx
    rw [(hd x hx').deriv]
    apply div_neg_of_neg_of_pos _ (pow_pos (hGpos x hx') 2)
    obtain ⟨c, hc, hE⟩ := exists_ratio_hasDerivAt_eq_ratio_slope F F' hx' hFc.continuousOn
      (fun y hy => hFd y hy.1) G G' hGc.continuousOn (fun y hy => hGd y hy.1)
    rw [hF0, hG0, sub_zero, sub_zero] at hE
    have hr := hanti hc.1 hx' hc.2
    simp only at hr
    have g1 := hG'pos c hc.1
    have g2 := hG'pos x hx'
    have g3 := hGpos x hx'
    rw [div_lt_div_iff₀ g2 g1] at hr
    -- hE : G x * F' c = F x * G' c ; hr : F' x * G' c < F' c * G' x
    have : (F' x * G x - F x * G' x) * G' c < 0 := by nlinarith
    nlinarith

theorem g78b_ampCQ_ratio {k : ℝ} (hk : 1 < k) :
    StrictAntiOn (fun u : ℝ => ((Real.log (k * u - 1 + 1) - Real.log (k * u - 1)) * (k * 1)) /
      ((Real.log ((k - 1) * u + 1) - Real.log ((k - 1) * u)) * ((k - 1) * 1))) (Set.Ioi 1) := by
  have ha : 0 < k - 1 := by linarith
  have hd : ∀ u : ℝ, 1 < u → HasDerivAt (fun u : ℝ => ((Real.log (k * u - 1 + 1) - Real.log (k * u - 1)) * (k * 1)) /
      ((Real.log ((k - 1) * u + 1) - Real.log ((k - 1) * u)) * ((k - 1) * 1)))
      (((1 / (k * u - 1 + 1) - 1 / (k * u - 1)) * (k * 1) * (k * 1) *
        ((Real.log ((k - 1) * u + 1) - Real.log ((k - 1) * u)) * ((k - 1) * 1)) -
        ((Real.log (k * u - 1 + 1) - Real.log (k * u - 1)) * (k * 1)) *
        ((1 / ((k - 1) * u + 1) - 1 / ((k - 1) * u)) * ((k - 1) * 1) * ((k - 1) * 1))) /
        ((Real.log ((k - 1) * u + 1) - Real.log ((k - 1) * u)) * ((k - 1) * 1)) ^ 2) u := by
    intro u hu
    have p1 : 0 < k * u - 1 := by nlinarith
    have p2 : 0 < (k - 1) * u := by nlinarith
    have a1 := ((g78b_L_hasDeriv p1).comp u (((hasDerivAt_id u).const_mul k).sub_const 1)).mul_const (k * 1)
    have a2 := ((g78b_L_hasDeriv p2).comp u ((hasDerivAt_id u).const_mul (k - 1))).mul_const ((k - 1) * 1)
    exact a1.div a2 (mul_pos (g78b_L_pos p2) (by linarith)).ne'
  apply strictAntiOn_of_deriv_neg (convex_Ioi 1)
  · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; intro u hu
    have hu' : 1 < u := hu
    rw [(hd u hu').deriv]
    have p1 : 0 < k * u - 1 := by nlinarith
    have p2 : 0 < (k - 1) * u := by nlinarith
    have Lp1 := g78b_L_pos p1
    have Lp2 := g78b_L_pos p2
    apply div_neg_of_neg_of_pos _ (pow_pos (mul_pos Lp2 (by linarith)) 2)
    have A := g78b_hh_anti p2 p1 (by nlinarith)
    simp only at A
    -- (ku-1) L(ku-1) < (au+1) L(au)
    have key : (k * u - 1) * (Real.log (k * u - 1 + 1) - Real.log (k * u - 1)) <
        ((k - 1) * u + 1) * (Real.log ((k - 1) * u + 1) - Real.log ((k - 1) * u)) := by
      have : (k * u - 1) * (Real.log (k * u - 1 + 1) - Real.log (k * u - 1)) <
          (k * u - 1 + 1) * (Real.log (k * u - 1 + 1) - Real.log (k * u - 1)) := by nlinarith
      linarith
    have e : (1 / (k * u - 1 + 1) - 1 / (k * u - 1)) * (k * 1) * (k * 1) *
        ((Real.log ((k - 1) * u + 1) - Real.log ((k - 1) * u)) * ((k - 1) * 1)) -
        ((Real.log (k * u - 1 + 1) - Real.log (k * u - 1)) * (k * 1)) *
        ((1 / ((k - 1) * u + 1) - 1 / ((k - 1) * u)) * ((k - 1) * 1) * ((k - 1) * 1)) =
        k * (k - 1) / u * ((k * u - 1) * (Real.log (k * u - 1 + 1) - Real.log (k * u - 1)) -
          ((k - 1) * u + 1) * (Real.log ((k - 1) * u + 1) - Real.log ((k - 1) * u))) /
          ((k * u - 1) * ((k - 1) * u + 1)) := by
      field_simp; ring
    rw [e]
    apply div_neg_of_neg_of_pos _ (by positivity)
    apply mul_neg_of_pos_of_neg (by positivity) (by linarith)

theorem g78b_ampCE_ratio {a : ℝ} (ha : 0 < a) :
    StrictAntiOn (fun w : ℝ => (Real.log (w + 1) - Real.log w) /
      ((Real.log (a + a * w + 1) - Real.log (a + a * w)) * (a * 1))) (Set.Ioi 0) := by
  have hd : ∀ w : ℝ, 0 < w → HasDerivAt (fun w : ℝ => (Real.log (w + 1) - Real.log w) /
      ((Real.log (a + a * w + 1) - Real.log (a + a * w)) * (a * 1)))
      (((1 / (w + 1) - 1 / w) * ((Real.log (a + a * w + 1) - Real.log (a + a * w)) * (a * 1)) -
        (Real.log (w + 1) - Real.log w) *
        ((1 / (a + a * w + 1) - 1 / (a + a * w)) * (a * 1) * (a * 1))) /
        ((Real.log (a + a * w + 1) - Real.log (a + a * w)) * (a * 1)) ^ 2) w := by
    intro w hw
    have p2 : 0 < a + a * w := by positivity
    have a2 := ((g78b_L_hasDeriv p2).comp w (((hasDerivAt_id w).const_mul a).const_add a)).mul_const (a * 1)
    exact (g78b_L_hasDeriv hw).div a2 (mul_pos (g78b_L_pos p2) (by linarith)).ne'
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; intro w hw
    have hw' : 0 < w := hw
    rw [(hd w hw').deriv]
    have p2 : 0 < a + a * w := by positivity
    have Lp2 := g78b_L_pos p2
    apply div_neg_of_neg_of_pos _ (pow_pos (mul_pos Lp2 (by linarith)) 2)
    have h1 := g78b_hh_ge p2
    have hy : 0 < (w + 1) / w := by positivity
    have hne : (w + 1) / w ≠ 1 := by
      intro h; rw [div_eq_one_iff_eq hw'.ne'] at h; linarith
    have hl := Real.log_lt_sub_one_of_pos hy hne
    rw [Real.log_div (by linarith) hw'.ne'] at hl
    have h2 : (w + 1) / w - 1 = 1 / w := by field_simp; ring
    have key : w * (Real.log (w + 1) - Real.log w) < 1 := by
      have : w * (Real.log (w + 1) - Real.log w) < w * (1 / w) :=
        mul_lt_mul_of_pos_left (by linarith) hw'
      rwa [mul_one_div_cancel hw'.ne'] at this
    have e : (1 / (w + 1) - 1 / w) * ((Real.log (a + a * w + 1) - Real.log (a + a * w)) * (a * 1)) -
        (Real.log (w + 1) - Real.log w) *
        ((1 / (a + a * w + 1) - 1 / (a + a * w)) * (a * 1) * (a * 1)) =
        a / (w + 1) * (w * (Real.log (w + 1) - Real.log w) -
          (a + a * w + 1) * (Real.log (a + a * w + 1) - Real.log (a + a * w))) /
          (w * (a + a * w + 1)) := by
      field_simp; ring
    rw [e]
    apply div_neg_of_neg_of_pos _ (by positivity)
    apply mul_neg_of_pos_of_neg (by positivity) (by linarith)
theorem g78b_te_eq (x : ℝ) : thermalEntropy x = g x / Real.log 2 := rfl

theorem g78b_te_sub_le {a b c d : ℝ} (h : g a - g b ≤ g c - g d) :
    thermalEntropy a - thermalEntropy b ≤ thermalEntropy c - thermalEntropy d := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  simp only [g78b_te_eq]
  rw [← sub_div, ← sub_div]
  exact div_le_div_of_nonneg_right h hl2.le

theorem g78b_kq_anti {m : ℝ} (hm : 1 ≤ m) :
    AntitoneOn (fun k : ℝ => g (k * m - 1) - g ((k - 1) * m)) (Set.Ici 1) := by
  have hd : ∀ k : ℝ, 1 < k → HasDerivAt (fun k : ℝ => g (k * m - 1) - g ((k - 1) * m))
      ((Real.log (k * m - 1 + 1) - Real.log (k * m - 1)) * (1 * m) -
        (Real.log ((k - 1) * m + 1) - Real.log ((k - 1) * m)) * (1 * m)) k := by
    intro k hk
    have p1 : 0 < k * m - 1 := by nlinarith
    have p2 : 0 < (k - 1) * m := by nlinarith
    exact ((g78b_g_hasDeriv p1).comp k (((hasDerivAt_id k).mul_const m).sub_const 1)).sub
      ((g78b_g_hasDeriv p2).comp k (((hasDerivAt_id k).sub_const 1).mul_const m))
  apply antitoneOn_of_deriv_nonpos (convex_Ici 1)
  · exact (g78b_g_cont.comp ((continuous_id.mul continuous_const).sub continuous_const)).sub
      (g78b_g_cont.comp ((continuous_id.sub continuous_const).mul continuous_const)) |>.continuousOn
  · rw [interior_Ici]; intro k hk; exact (hd k hk).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]; intro k hk
    have hk' : 1 < k := hk
    rw [(hd k hk').deriv]
    have p2 : 0 < (k - 1) * m := by nlinarith
    have := g78b_Lf_anti p2 (by nlinarith : (k - 1) * m ≤ k * m - 1)
    nlinarith

theorem g78b_kc_anti {m : ℝ} (hm : 1 ≤ m) (hm2 : m ≤ 201) :
    AntitoneOn (fun k : ℝ => g (k * 201 - 1) - g ((k - 1) * m)) (Set.Ici 1) := by
  have hd : ∀ k : ℝ, 1 < k → HasDerivAt (fun k : ℝ => g (k * 201 - 1) - g ((k - 1) * m))
      ((Real.log (k * 201 - 1 + 1) - Real.log (k * 201 - 1)) * (1 * 201) -
        (Real.log ((k - 1) * m + 1) - Real.log ((k - 1) * m)) * (1 * m)) k := by
    intro k hk
    have p1 : 0 < k * 201 - 1 := by nlinarith
    have p2 : 0 < (k - 1) * m := by nlinarith
    exact ((g78b_g_hasDeriv p1).comp k (((hasDerivAt_id k).mul_const 201).sub_const 1)).sub
      ((g78b_g_hasDeriv p2).comp k (((hasDerivAt_id k).sub_const 1).mul_const m))
  apply antitoneOn_of_deriv_nonpos (convex_Ici 1)
  · exact (g78b_g_cont.comp ((continuous_id.mul continuous_const).sub continuous_const)).sub
      (g78b_g_cont.comp ((continuous_id.sub continuous_const).mul continuous_const)) |>.continuousOn
  · rw [interior_Ici]; intro k hk; exact (hd k hk).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]; intro k hk
    have hk' : 1 < k := hk
    rw [(hd k hk').deriv]
    have ha : 0 < k - 1 := by linarith
    have p1 : 0 < k * 201 - 1 := by nlinarith
    have p2 : 0 < (k - 1) * m := by nlinarith
    have lo := g78b_Lf_lower p2
    have up := g78b_Lf_upper p1
    -- m * L(am) ≥ 2/(2a+1)
    have lo2 : 2 / (2 * (k - 1) + 1) ≤ m * (Real.log ((k - 1) * m + 1) - Real.log ((k - 1) * m)) := by
      have : 2 / (2 * (k - 1) + 1) ≤ m * (2 / (2 * ((k - 1) * m) + 1)) := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
      nlinarith
    have up2 : 201 * (Real.log (k * 201 - 1 + 1) - Real.log (k * 201 - 1)) ≤ 2 / (2 * (k - 1) + 1) := by
      have : 201 * ((2 * (k * 201 - 1) + 1) / (2 * (k * 201 - 1) * (k * 201 - 1 + 1))) ≤
          2 / (2 * (k - 1) + 1) := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
      nlinarith
    nlinarith

theorem g78b_part1 (k1 k2 : ℝ) (h1 : 1 ≤ k1) (h12 : k1 ≤ k2) :
    amplifierCQ k2 ⊆ amplifierCQ k1 ∧ amplifierCE k2 ⊆ amplifierCE k1 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have kq : ∀ s : ℝ, 0 ≤ s → thermalEntropy (k2 * s * 200 + k2 - 1) - thermalEntropy ((k2 - 1) * (s * 200 + 1)) ≤
      thermalEntropy (k1 * s * 200 + k1 - 1) - thermalEntropy ((k1 - 1) * (s * 200 + 1)) := by
    intro s hs
    apply g78b_te_sub_le
    have := g78b_kq_anti (m := s * 200 + 1) (by linarith) (Set.mem_Ici.2 h1)
      (Set.mem_Ici.2 (le_trans h1 h12)) h12
    simp only at this
    rw [show k2 * s * 200 + k2 - 1 = k2 * (s * 200 + 1) - 1 by ring,
      show k1 * s * 200 + k1 - 1 = k1 * (s * 200 + 1) - 1 by ring]
    exact this
  have kc : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → thermalEntropy (k2 * 200 + k2 - 1) - thermalEntropy ((k2 - 1) * (s * 200 + 1)) ≤
      thermalEntropy (k1 * 200 + k1 - 1) - thermalEntropy ((k1 - 1) * (s * 200 + 1)) := by
    intro s hs hs1
    apply g78b_te_sub_le
    have := g78b_kc_anti (m := s * 200 + 1) (by linarith) (by linarith) (Set.mem_Ici.2 h1)
      (Set.mem_Ici.2 (le_trans h1 h12)) h12
    simp only at this
    rw [show k2 * 200 + k2 - 1 = k2 * 201 - 1 by ring,
      show k1 * 200 + k1 - 1 = k1 * 201 - 1 by ring]
    exact this
  constructor
  · rintro r ⟨hr1, hr2, s, ⟨hs0, hs1⟩, c1, c2⟩
    refine ⟨hr1, hr2, s, ⟨hs0, hs1⟩, ?_, ?_⟩
    · have := kq s hs0; simp only at c1 ⊢; linarith
    · have := kc s hs0 hs1; simp only at c2 ⊢; linarith
  · rintro r ⟨hr1, hr2, s, ⟨hs0, hs1⟩, c1, c2⟩
    refine ⟨hr1, hr2, s, ⟨hs0, hs1⟩, ?_, ?_⟩
    · have := kc s hs0 hs1; simp only at c1 ⊢; linarith
    · have := kc s hs0 hs1; simp only at c2 ⊢; linarith
/-- CQ ratio: F(u)=g(ku-1)-g(k-1), G(u)=g((k-1)u)-g(k-1); F/G strictly anti on (1,inf) -/
theorem g78b_ampCQ_FG {k : ℝ} (hk : 1 < k) :
    StrictAntiOn (fun u : ℝ => (g (k * u - 1) - g (k - 1)) / (g ((k - 1) * u) - g (k - 1)))
      (Set.Ioi 1) := by
  have ha : 0 < k - 1 := by linarith
  refine g78b_lhop (x0 := 1) (by simp) (by simp)
    ((g78b_g_cont.comp ((continuous_const.mul continuous_id).sub continuous_const)).sub continuous_const)
    ((g78b_g_cont.comp (continuous_const.mul continuous_id)).sub continuous_const)
    (fun u hu => ((g78b_g_hasDeriv (by nlinarith : 0 < k * u - 1)).comp u
      (((hasDerivAt_id u).const_mul k).sub_const 1)).sub_const _)
    (fun u hu => ((g78b_g_hasDeriv (by nlinarith : 0 < (k - 1) * u)).comp u
      ((hasDerivAt_id u).const_mul (k - 1))).sub_const _)
    (fun u hu => mul_pos (g78b_L_pos (by nlinarith)) (by linarith)) ?_
  exact g78b_ampCQ_ratio hk

theorem g78b_ampCE_FG {a : ℝ} (ha : 0 < a) :
    StrictAntiOn (fun w : ℝ => (g w) / (g (a + a * w) - g a)) (Set.Ioi 0) := by
  refine g78b_lhop (x0 := 0) (by simp [g]) (by simp)
    g78b_g_cont
    ((g78b_g_cont.comp (continuous_const.add (continuous_const.mul continuous_id))).sub continuous_const)
    (fun w hw => g78b_g_hasDeriv hw)
    (fun w hw => ((g78b_g_hasDeriv (by positivity : 0 < a + a * w)).comp w
      (((hasDerivAt_id w).const_mul a).const_add a)).sub_const _)
    (fun w hw => mul_pos (g78b_L_pos (by positivity)) (by linarith)) ?_
  exact g78b_ampCE_ratio ha

theorem g78b_g_smono {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) : g x < g y := by
  have hc : ContinuousOn g (Set.Ici 0) := g78b_g_cont.continuousOn
  have : StrictMonoOn g (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hc
    rw [interior_Ici]; intro z hz
    rw [(g78b_g_hasDeriv hz).deriv]; exact g78b_L_pos hz
  exact this (Set.mem_Ici.2 hx) (Set.mem_Ici.2 (by linarith)) hxy

theorem g78b_G_le {a w : ℝ} (ha : 0 < a) (hw : 0 ≤ w) : g (a + a * w) - g a ≤ Real.log (w + 1) := by
  have p : 0 < a + a * w := by positivity
  have A := g78b_hh_anti ha p (by nlinarith)
  simp only at A
  rw [g78b_g_eq p, g78b_g_eq ha]
  rw [show a + a * w = a * (w + 1) by ring] at A ⊢
  generalize (a * (w + 1) + 1) * (Real.log (a * (w + 1) + 1) - Real.log (a * (w + 1))) = H1 at *
  generalize (a + 1) * (Real.log (a + 1) - Real.log a) = H2 at *
  rw [Real.log_mul ha.ne' (by linarith)]
  linarith

theorem g78b_g_gt_log {w : ℝ} (hw : 0 < w) : Real.log (w + 1) < g w := by
  rw [g78b_gte hw]
  have : 0 < Real.log (1 + 1 / w) := Real.log_pos (by have := one_div_pos.mpr hw; linarith)
  have := mul_pos hw this
  linarith

theorem g78b_ampCQ {k : ℝ} (hk : 1 < k) :
    cqTimeSharing
        (thermalEntropy (k * 200 + k - 1) - thermalEntropy (k - 1))
        (thermalEntropy (k * 200 + k - 1) - thermalEntropy ((k - 1) * 201)) ⊂ amplifierCQ k := by
  have ha : 0 < k - 1 := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hte : ∀ x, thermalEntropy x = g x / Real.log 2 := fun x => rfl
  set O := g (k * 200 + k - 1) with hO
  set G201 := g ((k - 1) * 201) - g (k - 1) with hG201
  set F201 := g (k * 201 - 1) - g (k - 1) with hF201
  have eO : k * 200 + k - 1 = k * 201 - 1 := by ring
  have hG201p : 0 < G201 := by
    have := g78b_g_smono ha.le (by nlinarith : k - 1 < (k - 1) * 201); linarith
  have hFG : G201 < F201 := by
    have := g78b_g_smono (by nlinarith) (by nlinarith : (k - 1) * 201 < k * 201 - 1); linarith
  have hratio : ∀ u : ℝ, 1 ≤ u → u ≤ 201 →
      F201 * (g ((k - 1) * u) - g (k - 1)) ≤ (g (k * u - 1) - g (k - 1)) * G201 := by
    intro u hu1 hu2
    rcases hu1.eq_or_lt with h | h
    · subst h; simp
    rcases hu2.eq_or_lt with h' | h'
    · subst h'; apply le_of_eq; rw [hF201, hG201]; try ring
    have := g78b_ampCQ_FG hk h (by norm_num : (1:ℝ) < 201) h'
    simp only at this
    have Gu : 0 < g ((k - 1) * u) - g (k - 1) := by
      have := g78b_g_smono ha.le (by nlinarith : k - 1 < (k - 1) * u); linarith
    rw [div_lt_div_iff₀ hG201p Gu] at this
    linarith
  have hsub : cqTimeSharing
        (thermalEntropy (k * 200 + k - 1) - thermalEntropy (k - 1))
        (thermalEntropy (k * 200 + k - 1) - thermalEntropy ((k - 1) * 201)) ⊆ amplifierCQ k := by
    rintro r ⟨hr1, hr2, t, ⟨ht0, ht1⟩, h1, h2⟩
    have hf : ContinuousOn (fun s : ℝ => g ((k - 1) * (s * 200 + 1))) (Set.Icc 0 1) :=
      (g78b_g_cont.comp (continuous_const.mul ((continuous_id.mul continuous_const).add
        continuous_const))).continuousOn
    have hmem : (1 - t) * g (k - 1) + t * g ((k - 1) * 201) ∈
        Set.Icc (g ((k - 1) * (0 * 200 + 1))) (g ((k - 1) * (1 * 200 + 1))) := by
      norm_num; constructor <;> nlinarith
    obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ := intermediate_value_Icc zero_le_one hf hmem
    simp only at hs
    have hr := hratio (s * 200 + 1) (by linarith) (by linarith)
    rw [hs, show (1 - t) * g (k - 1) + t * g ((k - 1) * 201) - g (k - 1) = t * G201 by
      rw [hG201]; ring] at hr
    have htF : t * F201 ≤ g (k * (s * 200 + 1) - 1) - g (k - 1) := by
      have : t * F201 * G201 ≤ (g (k * (s * 200 + 1) - 1) - g (k - 1)) * G201 := by linarith
      exact le_of_mul_le_mul_right this hG201p
    have h1' : r.1 * Real.log 2 ≤ (1 - t) * (O - g (k - 1)) := by
      have := mul_le_mul_of_nonneg_right h1 hl2.le
      rw [hte, hte, show (1 - t) * (O / Real.log 2 - g (k - 1) / Real.log 2) * Real.log 2 =
        (1 - t) * (O - g (k - 1)) by field_simp] at this
      exact this
    have h2' : r.2 * Real.log 2 ≤ t * (O - g ((k - 1) * 201)) := by
      have := mul_le_mul_of_nonneg_right h2 hl2.le
      rw [hte, hte, show t * (O / Real.log 2 - g ((k - 1) * 201) / Real.log 2) * Real.log 2 =
        t * (O - g ((k - 1) * 201)) by field_simp] at this
      exact this
    have hOF : O = F201 + g (k - 1) := by rw [hO, hF201, eO]; ring
    refine ⟨hr1, hr2, s, ⟨hs0, hs1⟩, ?_, ?_⟩
    · simp only
      rw [hte, hte, ← sub_div, le_div_iff₀ hl2, show k * s * 200 + k - 1 = k * (s * 200 + 1) - 1 by ring, hs]
      have htO : t * O = t * F201 + t * g (k - 1) := by rw [hOF]; ring
      nlinarith
    · simp only
      rw [hte, hte, ← sub_div, le_div_iff₀ hl2, hs, add_mul]
      have htO : t * O = t * F201 + t * g (k - 1) := by rw [hOF]; ring
      nlinarith
  refine (Set.ssubset_iff_of_subset hsub).2 ?_
  -- point at share 1/2, u = 101
  have F101p : g (k - 1) < g (k * 101 - 1) := g78b_g_smono ha.le (by nlinarith)
  have G101p : g (k - 1) < g ((k - 1) * 101) := g78b_g_smono ha.le (by nlinarith)
  have m1 : g (k * 101 - 1) ≤ O := by
    rw [hO, eO]; exact (g78b_g_smono (by nlinarith) (by nlinarith)).le
  have m2 : g ((k - 1) * 101) ≤ g (k * 101 - 1) := (g78b_g_smono (by nlinarith) (by nlinarith)).le
  have hstrict := g78b_ampCQ_FG hk (by norm_num : (1:ℝ) < 101) (by norm_num : (1:ℝ) < 201)
    (by norm_num)
  simp only at hstrict
  rw [div_lt_div_iff₀ hG201p (by linarith)] at hstrict
  refine ⟨((O - g (k * 101 - 1)) / Real.log 2,
    (g (k * 101 - 1) - g ((k - 1) * 101)) / Real.log 2), ?_, ?_⟩
  · refine ⟨div_nonneg (by linarith) hl2.le, div_nonneg (by linarith) hl2.le, 1/2,
      ⟨by norm_num, by norm_num⟩, ?_, ?_⟩
    · simp only; rw [hte, hte, show k * (1/2) * 200 + k - 1 = k * 101 - 1 by ring,
        show (k - 1) * (1/2 * 200 + 1) = (k - 1) * 101 by ring, sub_div]
    · simp only; rw [hte, hte, show (k - 1) * (1/2 * 200 + 1) = (k - 1) * 101 by ring, ← hO]
      apply le_of_eq; ring
  · rintro ⟨_, _, t, ⟨ht0, ht1⟩, h1, h2⟩
    simp only at h1 h2
    have h1' : O - g (k * 101 - 1) ≤ (1 - t) * (O - g (k - 1)) := by
      have := mul_le_mul_of_nonneg_right h1 hl2.le
      rw [hte, hte, show (1 - t) * (O / Real.log 2 - g (k - 1) / Real.log 2) * Real.log 2 =
        (1 - t) * (O - g (k - 1)) by field_simp, div_mul_cancel₀ _ hl2.ne'] at this
      exact this
    have h2' : g (k * 101 - 1) - g ((k - 1) * 101) ≤ t * (O - g ((k - 1) * 201)) := by
      have := mul_le_mul_of_nonneg_right h2 hl2.le
      rw [hte, hte, show t * (O / Real.log 2 - g ((k - 1) * 201) / Real.log 2) * Real.log 2 =
        t * (O - g ((k - 1) * 201)) by field_simp, div_mul_cancel₀ _ hl2.ne'] at this
      exact this
    have hOF : O = F201 + g (k - 1) := by rw [hO, hF201, eO]; ring
    rw [hOF] at h1' h2'
    rw [hG201] at hFG hstrict hG201p
    nlinarith [mul_nonneg (by nlinarith : (0:ℝ) ≤ (g (k * 101 - 1) - g (k - 1)) - t * F201)
      (by linarith : (0:ℝ) ≤ F201 - (g ((k - 1) * 201) - g (k - 1)))]
theorem g78b_ampCE {k : ℝ} (hk : 1 < k) :
    ceTimeSharing
        (thermalEntropy (k * 200 + k - 1) - thermalEntropy (k - 1))
        (thermalEntropy 200 + thermalEntropy (k * 200 + k - 1) -
          thermalEntropy ((k - 1) * 201)) (thermalEntropy 200) ⊂ amplifierCE k := by
  have ha : 0 < k - 1 := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hte : ∀ x, thermalEntropy x = g x / Real.log 2 := fun x => rfl
  set O := g (k * 200 + k - 1) with hO
  set G200 := g ((k - 1) * 201) - g (k - 1) with hG200
  have e201 : (k - 1) * 201 = (k - 1) + (k - 1) * 200 := by ring
  have hG200p : 0 < G200 := by
    have := g78b_g_smono ha.le (by nlinarith : k - 1 < (k - 1) * 201); linarith
  have g200p : 0 < g 200 := g78b_g_pos (by norm_num)
  have hGg : G200 < g 200 := by
    have h1 := g78b_G_le ha (by norm_num : (0:ℝ) ≤ 200)
    have h2 := g78b_g_gt_log (by norm_num : (0:ℝ) < 200)
    rw [hG200, e201]; linarith
  have hratio : ∀ w : ℝ, 0 ≤ w → w ≤ 200 →
      g 200 * (g ((k - 1) + (k - 1) * w) - g (k - 1)) ≤ g w * G200 := by
    intro w hw0 hw2
    rcases hw0.eq_or_lt with h | h
    · subst h; simp [g]
    rcases hw2.eq_or_lt with h' | h'
    · subst h'; apply le_of_eq; rw [hG200, e201]; try ring
    have := g78b_ampCE_FG ha h (by norm_num : (0:ℝ) < 200) h'
    simp only at this
    have Gw : 0 < g ((k - 1) + (k - 1) * w) - g (k - 1) := by
      have := g78b_g_smono ha.le (by nlinarith : k - 1 < (k - 1) + (k - 1) * w); linarith
    rw [div_lt_div_iff₀ (by rw [← e201]; exact hG200p) Gw] at this
    rw [hG200, e201]; linarith
  have hsub : ceTimeSharing
        (thermalEntropy (k * 200 + k - 1) - thermalEntropy (k - 1))
        (thermalEntropy 200 + thermalEntropy (k * 200 + k - 1) -
          thermalEntropy ((k - 1) * 201)) (thermalEntropy 200) ⊆ amplifierCE k := by
    rintro r ⟨hr1, hr2, t, ⟨ht0, ht1⟩, h1, h2⟩
    have hf : ContinuousOn (fun s : ℝ => g ((k - 1) * (s * 200 + 1))) (Set.Icc 0 1) :=
      (g78b_g_cont.comp (continuous_const.mul ((continuous_id.mul continuous_const).add
        continuous_const))).continuousOn
    have hmem : (1 - t) * g (k - 1) + t * g ((k - 1) * 201) ∈
        Set.Icc (g ((k - 1) * (0 * 200 + 1))) (g ((k - 1) * (1 * 200 + 1))) := by
      norm_num; constructor <;> nlinarith
    obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ := intermediate_value_Icc zero_le_one hf hmem
    simp only at hs
    have hr := hratio (s * 200) (by positivity) (by linarith)
    rw [show (k - 1) + (k - 1) * (s * 200) = (k - 1) * (s * 200 + 1) by ring, hs,
      show (1 - t) * g (k - 1) + t * g ((k - 1) * 201) - g (k - 1) = t * G200 by
      rw [hG200]; ring] at hr
    have htg : t * g 200 ≤ g (s * 200) := by
      have : t * g 200 * G200 ≤ g (s * 200) * G200 := by linarith
      exact le_of_mul_le_mul_right this hG200p
    have h1' : r.1 * Real.log 2 ≤ O - (1 - t) * g (k - 1) - t * g ((k - 1) * 201) + t * g 200 := by
      have := mul_le_mul_of_nonneg_right h1 hl2.le
      rw [hte, hte, hte, hte, show ((1 - t) * (O / Real.log 2 - g (k - 1) / Real.log 2) +
        t * (g 200 / Real.log 2 + O / Real.log 2 - g ((k - 1) * 201) / Real.log 2)) * Real.log 2 =
        O - (1 - t) * g (k - 1) - t * g ((k - 1) * 201) + t * g 200 by field_simp; ring] at this
      exact this
    have h2' : t * g 200 ≤ r.2 * Real.log 2 := by
      have := mul_le_mul_of_nonneg_right h2 hl2.le
      rw [hte, show t * (g 200 / Real.log 2) * Real.log 2 = t * g 200 by field_simp] at this
      exact this
    refine ⟨hr1, hr2, s, ⟨hs0, hs1⟩, ?_, ?_⟩
    · simp only
      rw [hte, hte, hte, show g (s * 200) / Real.log 2 + O / Real.log 2 -
        g ((k - 1) * (s * 200 + 1)) / Real.log 2 = (g (s * 200) + O -
        g ((k - 1) * (s * 200 + 1))) / Real.log 2 by ring, le_div_iff₀ hl2, hs]
      linarith
    · simp only
      rw [hte, hte, show O / Real.log 2 - g ((k - 1) * (s * 200 + 1)) / Real.log 2 + r.2 =
        (O - g ((k - 1) * (s * 200 + 1)) + r.2 * Real.log 2) / Real.log 2 by field_simp,
        le_div_iff₀ hl2, hs]
      linarith
  refine (Set.ssubset_iff_of_subset hsub).2 ?_
  have g100p : 0 < g 100 := g78b_g_pos (by norm_num)
  have G100p : g (k - 1) < g ((k - 1) * 101) := g78b_g_smono ha.le (by nlinarith)
  have m1 : g ((k - 1) * 101) ≤ O := by
    rw [hO]; exact (g78b_g_smono (by nlinarith) (by nlinarith)).le
  have hstrict := g78b_ampCE_FG ha (by norm_num : (0:ℝ) < 100) (by norm_num : (0:ℝ) < 200)
    (by norm_num)
  simp only at hstrict
  rw [show (k - 1) + (k - 1) * 100 = (k - 1) * 101 by ring,
    show (k - 1) + (k - 1) * 200 = (k - 1) * 201 by ring,
    div_lt_div_iff₀ hG200p (by linarith)] at hstrict
  refine ⟨((g 100 + O - g ((k - 1) * 101)) / Real.log 2, g 100 / Real.log 2), ?_, ?_⟩
  · refine ⟨div_nonneg (by linarith) hl2.le, div_nonneg (by linarith) hl2.le, 1/2,
      ⟨by norm_num, by norm_num⟩, ?_, ?_⟩
    · simp only; rw [hte, hte, hte, show (1:ℝ)/2 * 200 = 100 by norm_num,
        show (k - 1) * (100 + 1) = (k - 1) * 101 by ring, ← hO]
      apply le_of_eq; ring
    · simp only; rw [hte, hte, show (k - 1) * (1/2 * 200 + 1) = (k - 1) * 101 by ring, ← hO]
      apply le_of_eq; ring
  · rintro ⟨_, _, t, ⟨ht0, ht1⟩, h1, h2⟩
    simp only at h1 h2
    have h1' : g 100 + O - g ((k - 1) * 101) ≤
        O - (1 - t) * g (k - 1) - t * g ((k - 1) * 201) + t * g 200 := by
      have := mul_le_mul_of_nonneg_right h1 hl2.le
      rw [hte, hte, hte, hte, show ((1 - t) * (O / Real.log 2 - g (k - 1) / Real.log 2) +
        t * (g 200 / Real.log 2 + O / Real.log 2 - g ((k - 1) * 201) / Real.log 2)) * Real.log 2 =
        O - (1 - t) * g (k - 1) - t * g ((k - 1) * 201) + t * g 200 by field_simp; ring,
        div_mul_cancel₀ _ hl2.ne'] at this
      exact this
    have h2' : t * g 200 ≤ g 100 := by
      have := mul_le_mul_of_nonneg_right h2 hl2.le
      rw [hte, show t * (g 200 / Real.log 2) * Real.log 2 = t * g 200 by field_simp,
        div_mul_cancel₀ _ hl2.ne'] at this
      exact this
    have k1 : (g 100 - (g ((k - 1) * 101) - g (k - 1))) * g 200 ≤ t * (g 200 - G200) * g 200 :=
      mul_le_mul_of_nonneg_right (by rw [hG200]; linarith) g200p.le
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ g 100 - t * g 200) (by linarith : (0:ℝ) ≤ g 200 - G200)]

theorem g78b_eq1 : cqTimeSharing (thermalEntropy 200) (thermalEntropy 200) = amplifierCQ 1 := by
  have T0 : thermalEntropy 0 = 0 := by simp [thermalEntropy]
  have hTp : 0 < thermalEntropy 200 := div_pos (g78b_g_pos (by norm_num)) (Real.log_pos (by norm_num))
  ext r
  simp only [cqTimeSharing, amplifierCQ, cqFamily, Set.mem_setOf_eq]
  norm_num [T0]
  intro hr1 hr2
  constructor
  · rintro ⟨t, ⟨ht0, ht1⟩, h1, h2⟩
    refine ⟨1, ⟨by norm_num, le_rfl⟩, ?_, ?_⟩
    · norm_num; nlinarith
    · nlinarith
  · rintro ⟨s, ⟨hs0, hs1⟩, h1, h2⟩
    refine ⟨r.2 / thermalEntropy 200, ⟨by positivity, ?_⟩, ?_, ?_⟩
    · rw [div_le_one hTp]; linarith
    · rw [sub_mul, div_mul_cancel₀ _ hTp.ne']; linarith
    · rw [div_mul_cancel₀ _ hTp.ne']

theorem g78b_eq2 : ceTimeSharing (thermalEntropy 200) (2 * thermalEntropy 200) (thermalEntropy 200) =
      amplifierCE 1 := by
  have T0 : thermalEntropy 0 = 0 := by simp [thermalEntropy]
  have hTp : 0 < thermalEntropy 200 := div_pos (g78b_g_pos (by norm_num)) (Real.log_pos (by norm_num))
  ext r
  simp only [ceTimeSharing, amplifierCE, ceFamily, Set.mem_setOf_eq]
  norm_num [T0]
  intro hr1 hr2
  constructor
  · rintro ⟨t, ⟨ht0, ht1⟩, h1, h2⟩
    refine ⟨1, ⟨by norm_num, le_rfl⟩, ?_, ?_⟩
    · norm_num; nlinarith
    · nlinarith
  · rintro ⟨s, ⟨hs0, hs1⟩, h1, h2⟩
    have hmono : thermalEntropy (s * 200) ≤ thermalEntropy 200 :=
      g78b_te_mono (by positivity) (by nlinarith)
    by_cases hc : r.1 ≤ thermalEntropy 200
    · exact ⟨0, ⟨le_rfl, by norm_num⟩, by simpa using hc, by simpa using hr2⟩
    · have hc' : thermalEntropy 200 < r.1 := lt_of_not_ge hc
      have e : (r.1 - thermalEntropy 200) / thermalEntropy 200 * thermalEntropy 200 =
          r.1 - thermalEntropy 200 := div_mul_cancel₀ _ hTp.ne'
      refine ⟨(r.1 - thermalEntropy 200) / thermalEntropy 200,
        ⟨div_nonneg (by linarith) hTp.le, ?_⟩, ?_, ?_⟩
      · rw [div_le_one hTp]; linarith
      · nlinarith
      · linarith

/-- PDF pp.16-17, Section V and Figure 6: ordered-gain inclusion of the
N_S=200,N_B=0 displayed families, plus proper time-sharing improvement at gain>1.
At identity gain the straight-line families equal endpoint time sharing. -/
theorem solution :
    (∀ k1 k2 : ℝ, 1 ≤ k1 → k1 ≤ k2 →
      amplifierCQ k2 ⊆ amplifierCQ k1 ∧ amplifierCE k2 ⊆ amplifierCE k1) ∧
    (∀ gain : ℝ, 1 < gain →
      cqTimeSharing
        (thermalEntropy (gain * 200 + gain - 1) - thermalEntropy (gain - 1))
        (thermalEntropy (gain * 200 + gain - 1) -
          thermalEntropy ((gain - 1) * 201)) ⊂ amplifierCQ gain ∧
      ceTimeSharing
        (thermalEntropy (gain * 200 + gain - 1) - thermalEntropy (gain - 1))
        (thermalEntropy 200 + thermalEntropy (gain * 200 + gain - 1) -
          thermalEntropy ((gain - 1) * 201)) (thermalEntropy 200) ⊂ amplifierCE gain) ∧
    cqTimeSharing (thermalEntropy 200) (thermalEntropy 200) = amplifierCQ 1 ∧
    ceTimeSharing (thermalEntropy 200) (2 * thermalEntropy 200) (thermalEntropy 200) =
      amplifierCE 1 := by
  exact ⟨g78b_part1, fun gain hg => ⟨g78b_ampCQ hg, g78b_ampCE hg⟩, g78b_eq1, g78b_eq2⟩


end

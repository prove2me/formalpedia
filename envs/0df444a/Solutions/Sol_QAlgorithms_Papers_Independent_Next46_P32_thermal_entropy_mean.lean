-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P32.thermal_entropy_mean
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T15:59:07.04915+00:00
-- url     : https://prove2.me/submissions/065211a5-62a1-4edc-bafc-488f786e5e5e

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32

namespace G62T

noncomputable def g (v : ℝ) : ℝ := (v + 1) * Real.log (v + 1) - v * Real.log v

lemma g_zero : g 0 = 0 := by simp [g]

lemma g_cont : ContinuousOn g (Set.Ici 0) := by
  have h1 : ContinuousOn (fun v : ℝ => (v + 1) * Real.log (v + 1)) (Set.Ici 0) := by
    apply ContinuousOn.mul (continuousOn_id.add continuousOn_const)
    apply ContinuousOn.log (continuousOn_id.add continuousOn_const)
    intro x hx; have : (0:ℝ) ≤ x := hx; exact ne_of_gt (by simp; linarith)
  exact h1.sub Real.continuous_mul_log.continuousOn

lemma g_hasDeriv {v : ℝ} (hv : 0 < v) :
    HasDerivAt g (Real.log (v + 1) - Real.log v) v := by
  have h1 : HasDerivAt (fun v : ℝ => v + 1) 1 v := (hasDerivAt_id v).add_const 1
  have h2 := h1.mul (h1.log (by linarith))
  have h3 := (hasDerivAt_id v).mul (Real.hasDerivAt_log hv.ne')
  have := h2.sub h3
  refine this.congr_deriv ?_
  simp only [id, one_mul]
  field_simp
  ring

lemma g_strictMono : StrictMonoOn g (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) g_cont
  intro x hx
  rw [interior_Ici] at hx
  rw [(g_hasDeriv hx).deriv]
  have := Real.log_lt_log hx (by linarith : x < x + 1)
  linarith

lemma g_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ g v := by
  rw [← g_zero]; exact g_strictMono.monotoneOn (Set.mem_Ici.2 le_rfl) hv hv

lemma g_ge_log {v : ℝ} (hv : 0 ≤ v) : Real.log (v + 1) ≤ g v := by
  unfold g
  have hl : Real.log v ≤ Real.log (v + 1) := by
    rcases hv.eq_or_lt with h | h
    · subst h; simp
    · exact Real.log_le_log h (by linarith)
  nlinarith

/-- `k v = v log(1 + 1/v)` is monotone. -/
lemma k_mono : MonotoneOn (fun v : ℝ => v * (Real.log (v + 1) - Real.log v)) (Set.Ioi 0) := by
  have hd : ∀ v : ℝ, 0 < v → HasDerivAt (fun v : ℝ => v * (Real.log (v + 1) - Real.log v))
      (Real.log (v + 1) - Real.log v - 1 / (v + 1)) v := by
    intro v hv
    have h1 : HasDerivAt (fun v : ℝ => v + 1) 1 v := (hasDerivAt_id v).add_const 1
    have := (hasDerivAt_id v).mul ((h1.log (by linarith)).sub (Real.hasDerivAt_log hv.ne'))
    refine this.congr_deriv ?_
    simp only [id, Pi.sub_apply]
    field_simp
    ring
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; intro x hx; exact (hd x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]; intro x hx
    have hx0 : (0:ℝ) < x := hx
    rw [(hd x hx0).deriv]
    have := Real.one_sub_inv_le_log_of_pos (by positivity : (0:ℝ) < (x + 1) / x)
    rw [Real.log_div (by linarith) hx0.ne', inv_div] at this
    have e : 1 - x / (x + 1) = 1 / (x + 1) := by field_simp; ring
    linarith

/-- D c = g'(c), E c = g'(q c + q - 1). -/
noncomputable def Dg (c : ℝ) : ℝ := Real.log (c + 1) - Real.log c

noncomputable def ginv (s : ℝ) : ℝ := sInf {N : ℝ | 0 ≤ N ∧ s ≤ g N}

lemma ginv_spec {s : ℝ} (hs : 0 ≤ s) : 0 ≤ ginv s ∧ g (ginv s) = s := by
  have he : 0 ≤ Real.exp s := (Real.exp_pos s).le
  have hmem : s ∈ Set.Icc (g 0) (g (Real.exp s)) := by
    refine ⟨by rw [g_zero]; exact hs, ?_⟩
    have h1 := g_ge_log he
    have h2 : s ≤ Real.log (Real.exp s + 1) := by
      rw [← Real.log_exp s]
      exact Real.log_le_log (Real.exp_pos _) (by rw [Real.log_exp]; linarith)
    linarith
  obtain ⟨N, ⟨hN0, -⟩, hgN⟩ :=
    intermediate_value_Icc he (g_cont.mono Set.Icc_subset_Ici_self) hmem
  have : ginv s = N := by
    apply IsLeast.csInf_eq
    refine ⟨⟨hN0, hgN.ge⟩, ?_⟩
    rintro M ⟨hM0, hM⟩
    exact (g_strictMono.le_iff_le hN0 hM0).1 (hgN ▸ hM)
  rw [this]; exact ⟨hN0, hgN⟩

lemma ginv_g {y : ℝ} (hy : 0 ≤ y) : ginv (g y) = y := by
  obtain ⟨h0, h1⟩ := ginv_spec (g_nonneg hy)
  exact g_strictMono.injOn h0 hy h1

lemma Dg_pos {c : ℝ} (hc : 0 < c) : 0 < Dg c := by
  unfold Dg; have := Real.log_lt_log hc (by linarith : c < c + 1); linarith

lemma Dg_hasDeriv {c : ℝ} (hc : 0 < c) : HasDerivAt Dg (-1 / (c * (c + 1))) c := by
  have h1 : HasDerivAt (fun v : ℝ => v + 1) 1 c := (hasDerivAt_id c).add_const 1
  have := (h1.log (by linarith)).sub (Real.hasDerivAt_log hc.ne')
  refine this.congr_deriv ?_
  field_simp; ring

lemma m_anti : AntitoneOn (fun w : ℝ => (w + 1) * Dg w) (Set.Ioi 0) := by
  have hd : ∀ w : ℝ, 0 < w → HasDerivAt (fun w : ℝ => (w + 1) * Dg w) (Dg w - 1 / w) w := by
    intro w hw
    have := ((hasDerivAt_id w).add_const 1).mul (Dg_hasDeriv hw)
    refine this.congr_deriv ?_
    simp only [id]; field_simp; ring
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; intro x hx; exact (hd x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]; intro w hw
    have hw0 : (0:ℝ) < w := hw
    rw [(hd w hw0).deriv]
    have := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < (w + 1) / w)
    rw [Real.log_div (by linarith) hw0.ne'] at this
    have e : (w + 1) / w - 1 = 1 / w := by field_simp; ring
    unfold Dg; linarith

lemma ratio_mono {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1) :
    MonotoneOn (fun c => Dg (η * c) / Dg c) (Set.Ioi 0) := by
  have hdE : ∀ c : ℝ, 0 < c → HasDerivAt (fun c => Dg (η * c)) (η * (-1 / ((η * c) * (η * c + 1)))) c := by
    intro c hc
    have := (Dg_hasDeriv (mul_pos h0 hc)).comp c (by simpa using (hasDerivAt_id c).const_mul η :
      HasDerivAt (fun c : ℝ => η * c) η c)
    exact this.congr_deriv (by ring)
  have hdR : ∀ c : ℝ, 0 < c → HasDerivAt (fun c => Dg (η * c) / Dg c)
      ((η * (-1 / ((η * c) * (η * c + 1))) * Dg c - Dg (η * c) * (-1 / (c * (c + 1)))) / Dg c ^ 2) c :=
    fun c hc => (hdE c hc).div (Dg_hasDeriv hc) (Dg_pos hc).ne'
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · intro x hx; exact (hdR x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; intro x hx; exact (hdR x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]; intro c hc
    have hc0 : (0:ℝ) < c := hc
    rw [(hdR c hc0).deriv]
    apply div_nonneg _ (sq_nonneg _)
    have hec : 0 < η * c := mul_pos h0 hc0
    have hm := m_anti (Set.mem_Ioi.2 hec) (Set.mem_Ioi.2 hc0) (by nlinarith)
    simp only at hm
    have : η * (-1 / ((η * c) * (η * c + 1))) * Dg c - Dg (η * c) * (-1 / (c * (c + 1))) =
        ((η * c + 1) * Dg (η * c) - (c + 1) * Dg c) / (c * (c + 1) * (η * c + 1)) := by
      field_simp; ring
    rw [this]
    exact div_nonneg (by linarith) (by positivity)

noncomputable def phi (η s : ℝ) : ℝ := g (η * ginv s)

lemma slope_eq {η y1 y2 : ℝ} (he : 0 < η) (h0 : 0 ≤ y1) (h12 : y1 < y2) :
    ∃ c ∈ Set.Ioo y1 y2, (g (η * y2) - g (η * y1)) / (g y2 - g y1) =
      η * (Dg (η * c) / Dg c) := by
  have hGc : ContinuousOn (fun y => g (η * y)) (Set.Icc y1 y2) := by
    apply g_cont.comp (by fun_prop)
    intro y hy; simp only [Set.mem_Ici]; nlinarith [hy.1]
  have hgc : ContinuousOn g (Set.Icc y1 y2) := g_cont.mono (fun y hy => le_trans h0 hy.1)
  obtain ⟨c, hc, hcm⟩ := exists_ratio_hasDerivAt_eq_ratio_slope (fun y => g (η * y))
    (fun c => η * Dg (η * c)) h12 hGc
    (fun c hc => by
      have hc0 : 0 < c := lt_of_le_of_lt h0 hc.1
      have := (g_hasDeriv (mul_pos he hc0)).comp c (by simpa using (hasDerivAt_id c).const_mul η :
        HasDerivAt (fun c : ℝ => η * c) η c)
      exact this.congr_deriv (by unfold Dg; ring)) g Dg hgc
    (fun c hc => g_hasDeriv (lt_of_le_of_lt h0 hc.1))
  refine ⟨c, hc, ?_⟩
  have hc0 : 0 < c := lt_of_le_of_lt h0 hc.1
  have hD := Dg_pos hc0
  have hg : 0 < g y2 - g y1 := by have := g_strictMono h0 (le_trans h0 h12.le) h12; linarith
  rw [div_eq_iff hg.ne']
  have : η * (Dg (η * c) / Dg c) * (g y2 - g y1) = (g y2 - g y1) * (η * Dg (η * c)) / Dg c := by ring
  rw [this, hcm, mul_div_assoc, div_self hD.ne', mul_one]

lemma phi_convex {η : ℝ} (he : 0 < η) (he1 : η ≤ 1) : ConvexOn ℝ (Set.Ici 0) (phi η) := by
  apply convexOn_of_slope_mono_adjacent (convex_Ici 0)
  intro x y z hx hz hxy hyz
  have hx0 : (0:ℝ) ≤ x := hx
  have hy0 : 0 ≤ y := le_trans hx0 hxy.le
  have hz0 : (0:ℝ) ≤ z := hz
  obtain ⟨a0, ga⟩ := ginv_spec hx0
  obtain ⟨b0, gb⟩ := ginv_spec hy0
  obtain ⟨c0, gc⟩ := ginv_spec hz0
  have hab : ginv x < ginv y := by
    by_contra h; push Not at h
    have := g_strictMono.monotoneOn b0 a0 h; rw [ga, gb] at this; linarith
  have hbc : ginv y < ginv z := by
    by_contra h; push Not at h
    have := g_strictMono.monotoneOn c0 b0 h; rw [gb, gc] at this; linarith
  obtain ⟨c1, hc1, e1⟩ := slope_eq he a0 hab
  obtain ⟨c2, hc2, e2⟩ := slope_eq he b0 hbc
  unfold phi
  rw [ga, gb] at e1
  rw [gb, gc] at e2
  rw [e1, e2]
  apply mul_le_mul_of_nonneg_left _ he.le
  have hc10 : 0 < c1 := lt_of_le_of_lt a0 hc1.1
  exact ratio_mono he he1 (Set.mem_Ioi.2 hc10) (Set.mem_Ioi.2 (by linarith [hc1.2, hc2.1]))
    (by linarith [hc1.2, hc2.1])

end G62T

open QAlgorithms.Papers.Independent.Next46.P32
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

theorem solution (n : ℕ) (hn : 0 < n)
    (x : Fin n → ℝ) (x0 eta : ℝ) (hx : ∀ i, 0 ≤ x i) (hx0 : 0 ≤ x0)
    (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hmean : (∑ i, g (x i)) / (n : ℝ) = g x0) :
    g (eta * x0) ≤ (∑ i, g (eta * x i)) / (n : ℝ) := by
  have hg : ∀ v, g v = G62T.g v := fun v => rfl
  simp only [hg] at hmean ⊢
  rcases heta.eq_or_lt with h | he
  · subst h; simp [G62T.g_zero]
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hJ := (G62T.phi_convex he heta1).map_sum_le (t := Finset.univ) (w := fun _ => (1 / (n:ℝ)))
    (p := fun i => G62T.g (x i)) (fun _ _ => by positivity)
    (by simp; field_simp) (fun i _ => Set.mem_Ici.2 (G62T.g_nonneg (hx i)))
  simp only [smul_eq_mul] at hJ
  rw [← Finset.mul_sum, one_div_mul_eq_div, hmean] at hJ
  unfold G62T.phi at hJ
  rw [G62T.ginv_g hx0] at hJ
  simp only [G62T.ginv_g (hx _)] at hJ
  rw [← Finset.mul_sum, one_div_mul_eq_div] at hJ
  exact hJ

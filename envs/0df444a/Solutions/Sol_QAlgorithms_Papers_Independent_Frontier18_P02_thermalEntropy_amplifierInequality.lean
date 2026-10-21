-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P02.thermalEntropy_amplifierInequality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T13:29:25.128818+00:00
-- url     : https://prove2.me/submissions/e63bbe72-ba10-4743-af3e-41b5275430c1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P02

namespace G59P

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
noncomputable def Eg (q c : ℝ) : ℝ := Real.log (q * c + q) - Real.log (q * c + q - 1)

lemma Dg_pos {c : ℝ} (hc : 0 < c) : 0 < Dg c := by
  unfold Dg; have := Real.log_lt_log hc (by linarith : c < c + 1); linarith

lemma Eg_pos {q c : ℝ} (hq : 1 < q) (hc : 0 < c) : 0 < Eg q c := by
  unfold Eg
  have h1 : 0 < q * c + q - 1 := by nlinarith
  have := Real.log_lt_log h1 (by linarith : q * c + q - 1 < q * c + q); linarith

lemma ratio_mono {q : ℝ} (hq : 1 < q) :
    MonotoneOn (fun c => Eg q c / Dg c) (Set.Ioi 0) := by
  have hdD : ∀ c : ℝ, 0 < c → HasDerivAt Dg (1 / (c + 1) - 1 / c) c := by
    intro c hc
    have h1 : HasDerivAt (fun v : ℝ => v + 1) 1 c := (hasDerivAt_id c).add_const 1
    have := (h1.log (by linarith)).sub (Real.hasDerivAt_log hc.ne')
    refine this.congr_deriv ?_
    simp
  have hdE : ∀ c : ℝ, 0 < c → HasDerivAt (Eg q) (1 / (c + 1) - q / (q * c + q - 1)) c := by
    intro c hc
    have h1 : 0 < q * c + q - 1 := by nlinarith
    have a1 : HasDerivAt (fun v : ℝ => q * v + q) q c := by
      simpa using ((hasDerivAt_id c).const_mul q).add_const q
    have a2 : HasDerivAt (fun v : ℝ => q * v + q - 1) q c := a1.sub_const 1
    have := (a1.log (by nlinarith)).sub (a2.log h1.ne')
    refine this.congr_deriv ?_
    field_simp
  have hdR : ∀ c : ℝ, 0 < c → HasDerivAt (fun c => Eg q c / Dg c)
      (((1 / (c + 1) - q / (q * c + q - 1)) * Dg c - Eg q c * (1 / (c + 1) - 1 / c)) / Dg c ^ 2) c :=
    fun c hc => (hdE c hc).div (hdD c hc) (Dg_pos hc).ne'
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · intro x hx; exact (hdR x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; intro x hx; exact (hdR x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]; intro c hc
    have hc0 : (0:ℝ) < c := hc
    rw [(hdR c hc0).deriv]
    apply div_nonneg _ (sq_nonneg _)
    have h1 : 0 < q * c + q - 1 := by nlinarith
    have hk := k_mono (Set.mem_Ioi.2 hc0) (Set.mem_Ioi.2 h1) (by nlinarith)
    simp only at hk
    have hkE : (q * c + q - 1) * (Real.log (q * c + q - 1 + 1) - Real.log (q * c + q - 1)) =
        (q * c + q - 1) * Eg q c := by
      unfold Eg; ring_nf
    rw [hkE] at hk
    have hD := Dg_pos hc0
    have hE := Eg_pos hq hc0
    -- numerator = (c D - (qc+q-1) E)·(-1)/(c (c+1) (qc+q-1)) ... show directly
    have n1 : q * c + q - 1 ≠ 0 := h1.ne'
    have n2 : c + 1 ≠ 0 := by linarith
    have n3 : c ≠ 0 := hc0.ne'
    have e1 : 1 / (c + 1) - q / (q * c + q - 1) = -1 / ((c + 1) * (q * c + q - 1)) := by
      rw [div_sub_div _ _ n2 n1]; congr 1; ring
    have e2 : 1 / (c + 1) - 1 / c = -1 / (c * (c + 1)) := by
      rw [div_sub_div _ _ n2 n3, mul_comm (c + 1) c]; congr 1; ring
    rw [e1, e2]
    have : (-1 / ((c + 1) * (q * c + q - 1))) * Dg c - Eg q c * (-1 / (c * (c + 1))) =
        ((q * c + q - 1) * Eg q c - c * Dg c) / (c * (c + 1) * (q * c + q - 1)) := by
      generalize q * c + q - 1 = w at n1 ⊢
      field_simp
      ring
    rw [this]
    apply div_nonneg _ (by positivity)
    have : c * Dg c = c * (Real.log (c + 1) - Real.log c) := rfl
    linarith


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

noncomputable def phi (q s : ℝ) : ℝ := g (q * ginv s + q - 1)

lemma G_hasDeriv {q c : ℝ} (hq : 1 < q) (hc : 0 < c) :
    HasDerivAt (fun y => g (q * y + q - 1)) (q * Eg q c) c := by
  have h1 : 0 < q * c + q - 1 := by nlinarith
  have a : HasDerivAt (fun y : ℝ => q * y + q - 1) q c := by
    simpa using (((hasDerivAt_id c).const_mul q).add_const q).sub_const 1
  have := (g_hasDeriv h1).comp c a
  refine this.congr_deriv ?_
  unfold Eg; ring_nf

lemma slope_eq {q y1 y2 : ℝ} (hq : 1 < q) (h0 : 0 ≤ y1) (h12 : y1 < y2) :
    ∃ c ∈ Set.Ioo y1 y2, (g (q * y2 + q - 1) - g (q * y1 + q - 1)) / (g y2 - g y1) =
      q * (Eg q c / Dg c) := by
  have hGc : ContinuousOn (fun y => g (q * y + q - 1)) (Set.Icc y1 y2) := by
    apply g_cont.comp (by fun_prop)
    intro y hy; simp only [Set.mem_Ici]; nlinarith [hy.1]
  have hgc : ContinuousOn g (Set.Icc y1 y2) := g_cont.mono (fun y hy => le_trans h0 hy.1)
  obtain ⟨c, hc, hcm⟩ := exists_ratio_hasDerivAt_eq_ratio_slope (fun y => g (q * y + q - 1))
    (fun c => q * Eg q c) h12 hGc (fun c hc => G_hasDeriv hq (lt_of_le_of_lt h0 hc.1)) g Dg hgc
    (fun c hc => g_hasDeriv (lt_of_le_of_lt h0 hc.1))
  refine ⟨c, hc, ?_⟩
  have hc0 : 0 < c := lt_of_le_of_lt h0 hc.1
  have hD := Dg_pos hc0
  have hg : 0 < g y2 - g y1 := by have := g_strictMono h0 (le_trans h0 h12.le) h12; linarith
  rw [div_eq_iff hg.ne']
  have : q * (Eg q c / Dg c) * (g y2 - g y1) = (g y2 - g y1) * (q * Eg q c) / Dg c := by ring
  rw [this, hcm, mul_div_assoc, div_self hD.ne', mul_one]

lemma phi_convex {q : ℝ} (hq : 1 < q) : ConvexOn ℝ (Set.Ici 0) (phi q) := by
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
  obtain ⟨c1, hc1, e1⟩ := slope_eq hq a0 hab
  obtain ⟨c2, hc2, e2⟩ := slope_eq hq b0 hbc
  unfold phi
  rw [ga, gb] at e1
  rw [gb, gc] at e2
  rw [e1, e2]
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  have hc10 : 0 < c1 := lt_of_le_of_lt a0 hc1.1
  exact ratio_mono hq (Set.mem_Ioi.2 hc10) (Set.mem_Ioi.2 (by linarith [hc1.2, hc2.1]))
    (by linarith [hc1.2, hc2.1])

end G59P

open QAlgorithms.Papers.Independent.Frontier18.P02
open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

theorem solution (n : ℕ) (hn : 0 < n)
    (q y0 : ℝ) (hq : 1 < q) (hy0 : 0 ≤ y0)
    (p y : Fin n → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hp_sum : ∑ x, p x = 1) (hy : ∀ x, 0 ≤ y x)
    (hentropy : ∑ x, p x * thermalEntropy (y x) = thermalEntropy y0) :
    thermalEntropy (q * y0 + q - 1) ≤
      ∑ x, p x * thermalEntropy (q * y x + q - 1) := by
  have hte : ∀ v, thermalEntropy v = G59P.g v / Real.log 2 := fun v => rfl
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  simp only [hte] at hentropy ⊢
  have hent : ∑ x, p x * G59P.g (y x) = G59P.g y0 := by
    have : ∑ x, p x * (G59P.g (y x) / Real.log 2) = (∑ x, p x * G59P.g (y x)) / Real.log 2 := by
      rw [Finset.sum_div]; congr 1; funext x; ring
    rw [this, div_left_inj' hl2.ne'] at hentropy
    exact hentropy
  have hJ := (G59P.phi_convex hq).map_sum_le (t := Finset.univ) (w := p) (p := fun x => G59P.g (y x))
    (fun x _ => hp x) hp_sum (fun x _ => Set.mem_Ici.2 (G59P.g_nonneg (hy x)))
  simp only [smul_eq_mul] at hJ
  rw [hent] at hJ
  unfold G59P.phi at hJ
  rw [G59P.ginv_g hy0] at hJ
  simp only [G59P.ginv_g (hy _)] at hJ
  have : ∑ x, p x * (G59P.g (q * y x + q - 1) / Real.log 2) =
      (∑ x, p x * G59P.g (q * y x + q - 1)) / Real.log 2 := by
    rw [Finset.sum_div]; congr 1; funext x; ring
  rw [this]
  exact div_le_div_of_nonneg_right hJ hl2.le


-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P09.secondDerivative_order
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:08:47.646152+00:00
-- url     : https://prove2.me/submissions/ff6c1417-ee8b-4f80-beb3-a906e336deba

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P09
open QAlgorithms.Papers.Independent.Claimed50.P09

theorem g57b_sd_nonneg (g : ℝ → ℝ) (hg : Differentiable ℝ g)
    (hg2 : Differentiable ℝ (deriv g)) (hg0 : g 0 = 0) (hgs : deriv g 0 = 0)
    (hpos : ∀ x, 0 ≤ g x) : 0 ≤ deriv (deriv g) 0 := by
  by_contra hc
  rw [not_le] at hc
  have hd : HasDerivAt (deriv g) (deriv (deriv g) 0) 0 := (hg2 0).hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope] at hd
  have h1 : Filter.Tendsto (slope (deriv g) 0) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (deriv (deriv g) 0)) := hd.mono_left (nhdsWithin_mono _ (by
        intro x hx; exact ne_of_gt hx))
  have h2 : ∀ᶠ x in nhdsWithin (0:ℝ) (Set.Ioi 0), slope (deriv g) 0 x < 0 :=
    h1.eventually (gt_mem_nhds hc)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h2
  obtain ⟨δ, hδ, hδ'⟩ := h2
  have hneg : ∀ x, 0 < x → x < δ → deriv g x < 0 := by
    intro x hx hxδ
    have := hδ' (by rw [Real.dist_eq, sub_zero, abs_of_pos hx]; exact hxδ) hx
    rw [slope_def_field, hgs, sub_zero, sub_zero] at this
    exact (div_neg_iff.mp this).elim (fun h => absurd h.2 (not_lt.mpr hx.le)) (fun h => h.1)
  have hanti : StrictAntiOn g (Set.Icc 0 (δ/2)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 (δ/2)) hg.continuous.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    exact hneg x hx.1 (by linarith [hx.2])
  have := hanti ⟨le_refl 0, by linarith⟩ ⟨by linarith, le_refl _⟩ (by linarith)
  linarith [hpos (δ/2)]

theorem solution (f h : ℝ → ℝ)
    (hf : Differentiable ℝ f) (hh : Differentiable ℝ h)
    (hf2 : Differentiable ℝ (deriv f)) (hh2 : Differentiable ℝ (deriv h))
    (hf0 : f 0 = 0) (hh0 : h 0 = 0)
    (hfSlope : deriv f 0 = 0) (hhSlope : deriv h 0 = 0)
    (horder : ∀ x : ℝ, f x ≤ h x) :
    deriv (deriv f) 0 ≤ deriv (deriv h) 0 := by
  have hd1 : deriv (fun x => h x - f x) = fun x => deriv h x - deriv f x := by
    funext x; exact deriv_sub (hh x) (hf x)
  have key := g57b_sd_nonneg (fun x => h x - f x) (hh.sub hf)
    (by rw [hd1]; exact hh2.sub hf2) (by simp [hf0, hh0]) (by rw [hd1]; simp [hfSlope, hhSlope])
    (fun x => by linarith [horder x])
  rw [hd1, deriv_fun_sub (hh2 0) (hf2 0)] at key
  linarith

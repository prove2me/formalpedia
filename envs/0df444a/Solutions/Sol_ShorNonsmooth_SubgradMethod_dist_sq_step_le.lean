-- Prove2me | solution 1 for ShorNonsmooth.SubgradMethod.dist_sq_step_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T18:37:19.550995+00:00
-- url     : https://prove2.me/submissions/1293a0da-b203-41b3-a5c1-bcc8ca3f2481

import Mathlib
import Definitions.Def_ShorNonsmooth_SubgradMethod_SubgradientMethod

open Filter Topology

open ShorNonsmooth.SubgradMethod in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (xk gk xstar : EuclideanSpace ℝ (Fin n))
    (hgk : ShorNonsmooth.AlmostDiff.IsSubgradient f xk gk) (hgk0 : gk ≠ 0) (hxstar : xstar ∈ MinSet f)
    (h : ℝ) (hh : 0 < h) :
    ‖xk - (h / ‖gk‖) • gk - xstar‖ ^ 2 ≤
      ‖xk - xstar‖ ^ 2 + h ^ 2 - 2 * h * Metric.infDist xstar {x | f x = f xk} := by
  have hg : 0 < ‖gk‖ := norm_pos_iff.mpr hgk0
  have hcont : Continuous f :=
    continuousOn_univ.mp (hf.continuousOn isOpen_univ)
  set d : ℝ := inner ℝ gk (xk - xstar) / ‖gk‖ with hd
  set v : EuclideanSpace ℝ (Fin n) := ‖gk‖⁻¹ • gk with hv
  have hvn : ‖v‖ = 1 := by
    rw [hv, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hg.ne']
  have hmin : f xstar ≤ f xk := hxstar xk
  have hsub := hgk xstar
  have hd0 : 0 ≤ d := by
    have : inner ℝ gk (xstar - xk) ≤ 0 := by linarith
    have h2 : inner ℝ gk (xk - xstar) = - inner ℝ gk (xstar - xk) := by
      rw [← inner_neg_right, neg_sub]
    rw [hd, h2]
    exact div_nonneg (by linarith) hg.le
  -- value at the far end
  have hfar : f xk ≤ f (xstar + d • v) := by
    have := hgk (xstar + d • v)
    have hin : inner ℝ gk (xstar + d • v - xk) = 0 := by
      have e : xstar + d • v - xk = d • v - (xk - xstar) := by abel
      rw [e, inner_sub_right, hv, inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq, hd]
      field_simp
      ring
    linarith
  have hφ : ContinuousOn (fun s : ℝ => f (xstar + s • v)) (Set.Icc 0 d) :=
    (hcont.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
  obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc hd0 hφ
    (show f xk ∈ Set.Icc (f (xstar + (0:ℝ) • v)) (f (xstar + d • v)) by
      simp only [zero_smul, add_zero]; exact ⟨hmin, hfar⟩)
  have hinf : Metric.infDist xstar {x | f x = f xk} ≤ d := by
    calc Metric.infDist xstar {x | f x = f xk} ≤ dist xstar (xstar + s • v) :=
          Metric.infDist_le_dist_of_mem (by simpa using hfs)
      _ = s := by
          rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, hvn, mul_one,
            Real.norm_eq_abs, abs_of_nonneg hs.1]
      _ ≤ d := hs.2
  have hexp : ‖xk - (h / ‖gk‖) • gk - xstar‖ ^ 2 = ‖xk - xstar‖ ^ 2 + h ^ 2 - 2 * h * d := by
    have e : xk - (h / ‖gk‖) • gk - xstar = (xk - xstar) - (h / ‖gk‖) • gk := by abel
    rw [e, @norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hh hg), real_inner_comm, hd]
    field_simp
    ring
  rw [hexp]
  nlinarith

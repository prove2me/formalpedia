-- Prove2me | solution 1 for ShorNonsmooth.AlmostDiff.convex_dirDeriv_bounded_on_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T16:42:30.66324+00:00
-- url     : https://prove2.me/submissions/fdc25223-647f-4918-94b9-f73791d9a8dd

import Mathlib

open Set Filter Topology Metric in
theorem p2m8d_aux_line {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (x v : EuclideanSpace ℝ (Fin n)) :
    ConvexOn ℝ Set.univ (fun t : ℝ => f (x + t • v)) := by
  refine ⟨convex_univ, ?_⟩
  intro s _ t _ a b ha hb hab
  have h := hf.2 (mem_univ (x + s • v)) (mem_univ (x + t • v)) ha hb hab
  have e : a • (x + s • v) + b • (x + t • v) = x + (a • s + b • t) • v := by
    rw [smul_add, smul_add, smul_smul, smul_smul, add_smul, smul_eq_mul, smul_eq_mul]
    have : x = (a + b) • x := by rw [hab, one_smul]
    conv_rhs => rw [this]
    rw [add_smul]; abel
  rw [e] at h
  simpa only [smul_eq_mul] using h

open Set Filter Topology Metric in
theorem p2m8d_main {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : Bornology.IsBounded S) :
    ∃ C : ℝ, ∀ x ∈ S, ∀ v : EuclideanSpace ℝ (Fin n), ∃ d : ℝ,
      Filter.Tendsto (fun t : ℝ => (f (x + t • v) - f x) / t) (nhdsWithin 0 (Set.Ioi 0))
        (nhds d) ∧ |d| ≤ C * ‖v‖ := by
  obtain ⟨R, hR⟩ := hS.subset_ball 0
  have hcont : Continuous f := continuousOn_univ.mp (hf.continuousOn isOpen_univ)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + 2)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hL := (hf.subset (subset_univ _) (convex_ball (0 : EuclideanSpace ℝ (Fin n)) (R + 2))).lipschitzOnWith_of_abs_le
    (ε := 1) one_pos (M := M) (fun a ha => by
      have := hM a (mem_closedBall.2 ha.le)
      simpa [Real.norm_eq_abs] using this)
  refine ⟨(2 * M / 1).toNNReal, fun x hx v => ?_⟩
  set K : ℝ := ((2 * M / 1).toNNReal : ℝ)
  have hg := p2m8d_aux_line f hf x v
  have hint : (0 : ℝ) ∈ interior (univ : Set ℝ) := by simp
  have hd := hg.hasDerivWithinAt_rightDeriv_of_mem_interior hint
  rw [hasDerivWithinAt_iff_tendsto_slope] at hd
  have hlim : Tendsto (fun t : ℝ => (f (x + t • v) - f x) / t) (𝓝[>] 0)
      (𝓝 (derivWithin (fun t : ℝ => f (x + t • v)) (Ioi 0) 0)) := by
    have hset : Ioi (0 : ℝ) \ {0} = Ioi 0 := by
      ext t; simp only [Set.mem_sdiff, mem_Ioi, mem_singleton_iff]
      exact ⟨fun h => h.1, fun h => ⟨h, h.ne'⟩⟩
    rw [hset] at hd
    refine hd.congr (fun t => ?_)
    simp [slope_def_field, div_eq_mul_inv]
  refine ⟨_, hlim, ?_⟩
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), |(f (x + t • v) - f x) / t| ≤ K * ‖v‖ := by
    have hpos : (0 : ℝ) < 1 / (‖v‖ + 1) := by positivity
    filter_upwards [Ioo_mem_nhdsGT hpos] with t ht
    have ht0 : 0 < t := ht.1
    have hxb : x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (R + 2 - 1) := by
      have := hR hx
      rw [mem_ball] at this ⊢; linarith
    have htv : ‖t • v‖ < 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      have h2 : t * (‖v‖ + 1) < 1 := by
        have := ht.2; rw [lt_div_iff₀ (by positivity)] at this; exact this
      nlinarith [norm_nonneg v]
    have hyb : x + t • v ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (R + 2 - 1) := by
      have := hR hx
      rw [mem_ball] at this ⊢
      calc dist (x + t • v) 0 ≤ dist x 0 + ‖t • v‖ := by
            rw [dist_eq_norm, dist_eq_norm, sub_zero, sub_zero]; exact norm_add_le _ _
        _ < R + 2 - 1 := by linarith
    have h1 := hL.dist_le_mul (x + t • v) hyb x hxb
    rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht0] at h1
    rw [abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
    calc |f (x + t • v) - f x| ≤ K * (t * ‖v‖) := h1
      _ = K * ‖v‖ * t := by ring
  exact le_of_tendsto hlim.abs hev

theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : Bornology.IsBounded S) :
    ∃ C : ℝ, ∀ x ∈ S, ∀ v : EuclideanSpace ℝ (Fin n), ∃ d : ℝ,
      Filter.Tendsto (fun t : ℝ => (f (x + t • v) - f x) / t) (nhdsWithin 0 (Set.Ioi 0))
        (nhds d) ∧ |d| ≤ C * ‖v‖ := by
  exact p2m8d_main f hf S hS

-- Prove2me | solution 1 for ShorNonsmooth.AlmostDiff.almostGradients_nonempty_bounded_closed
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T07:06:28.931835+00:00
-- url     : https://prove2.me/submissions/d01a6a22-aa1d-4c54-8cc1-4f23d603a99e

import Mathlib
import Definitions.Def_ShorNonsmooth_AlmostDiff_AlmostDifferentiable
import Definitions.Def_ShorNonsmooth_AlmostDiff_almostGradients

namespace E6c2d262

open Metric Filter Topology

theorem mem_iff {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x g : EuclideanSpace ℝ (Fin n)) :
    g ∈ ShorNonsmooth.AlmostDiff.almostGradients f x ↔
      ∀ ε > 0, ∃ y, DifferentiableAt ℝ f y ∧ dist y x < ε ∧ dist (gradient f y) g < ε := by
  constructor
  · rintro ⟨xs, hxs, hd, hc⟩ ε hε
    have h1 := mapClusterPt_iff_frequently.1 hc (ball g ε) (ball_mem_nhds g hε)
    have h2 : ∀ᶠ k in atTop, xs k ∈ ball x ε := hxs.eventually_mem (ball_mem_nhds x hε)
    obtain ⟨k, hk1, hk2⟩ := (h1.and_eventually h2).exists
    exact ⟨xs k, hd k, hk2, hk1⟩
  · intro h
    choose y hy using fun k : ℕ => h (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat
    refine ⟨y, ?_, fun k => (hy k).1, ?_⟩
    · rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun k => dist_nonneg) (fun k => (hy k).2.1.le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    · apply Filter.Tendsto.mapClusterPt
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun k => dist_nonneg) (fun k => (hy k).2.2.le)
        tendsto_one_div_add_atTop_nhds_zero_nat

theorem grad_bound {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (L : NNReal) (hL : LipschitzOnWith L f (ball x 2)) (y : EuclideanSpace ℝ (Fin n))
    (hy : dist y x < 1) : ‖gradient f y‖ ≤ L := by
  have hs : ball x 2 ∈ 𝓝 y := by
    apply isOpen_ball.mem_nhds
    rw [mem_ball]; linarith
  have := norm_fderiv_le_of_lipschitzOn (𝕜 := ℝ) hs hL
  rw [gradient, LinearIsometryEquiv.norm_map]
  exact this

end E6c2d262

-- Shor (1985), p. 18, Theorem 1.14: G(x) is nonempty, bounded and closed.
open ShorNonsmooth.AlmostDiff Metric Filter Topology in
theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : AlmostDifferentiable f)
    (x : EuclideanSpace ℝ (Fin n)) :
    (almostGradients f x).Nonempty ∧ Bornology.IsBounded (almostGradients f x) ∧
      IsClosed (almostGradients f x) := by
  obtain ⟨L, hL⟩ := hf.1 (ball x 2) isBounded_ball
  -- density of differentiability points
  have hdense : ∀ ε > 0, ∃ y, DifferentiableAt ℝ f y ∧ dist y x < ε := by
    intro ε hε
    by_contra hcon
    push Not at hcon
    have hsub : ball x ε ⊆ {y | ¬ DifferentiableAt ℝ f y} := by
      intro y hy hdy
      have := hcon y hdy
      rw [mem_ball] at hy
      linarith
    have h0 : MeasureTheory.volume {y | ¬ DifferentiableAt ℝ f y} = 0 :=
      MeasureTheory.ae_iff.1 hf.2.1
    have := MeasureTheory.measure_mono_null hsub h0
    exact (measure_ball_pos MeasureTheory.volume x hε).ne' this
  refine ⟨?_, ?_, ?_⟩
  · choose y hy using fun k : ℕ => hdense (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat
    have hyx : Tendsto y atTop (𝓝 x) := by
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun k => dist_nonneg) (fun k => (hy k).2.le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hlt1 : ∀ k : ℕ, dist (y k) x < 1 := by
      intro k
      have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      exact lt_of_lt_of_le (hy k).2 h1
    have hmem : ∀ k, gradient f (y k) ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) L := by
      intro k
      rw [mem_closedBall, dist_zero_right]
      exact E6c2d262.grad_bound f x L hL (y k) (hlt1 k)
    obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (L : ℝ)).tendsto_subseq hmem
    refine ⟨a, y ∘ φ, hyx.comp hφ.tendsto_atTop, fun k => (hy (φ k)).1, ?_⟩
    exact hlim.mapClusterPt
  · refine (isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin n))) (r := (L : ℝ))).subset ?_
    intro g hg
    rw [mem_closedBall, dist_zero_right]
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨y, -, hyx, hyg⟩ := (E6c2d262.mem_iff f x g).1 hg (min ε 1) (lt_min hε one_pos)
    have hb := E6c2d262.grad_bound f x L hL y (lt_of_lt_of_le hyx (min_le_right _ _))
    have : ‖g‖ ≤ ‖gradient f y‖ + dist (gradient f y) g := by
      rw [dist_eq_norm]
      have := norm_sub_norm_le g (gradient f y)
      rw [← norm_neg (gradient f y - g), neg_sub] at *
      linarith [norm_le_insert' g (gradient f y)]
    have := min_le_left ε 1
    linarith
  · apply isClosed_of_closure_subset
    intro g hg
    rw [E6c2d262.mem_iff]
    intro ε hε
    obtain ⟨g', hg', hgg'⟩ := Metric.mem_closure_iff.1 hg (ε / 2) (by positivity)
    obtain ⟨y, hdy, hyx, hyg⟩ := (E6c2d262.mem_iff f x g').1 hg' (ε / 2) (by positivity)
    refine ⟨y, hdy, by linarith, ?_⟩
    calc dist (gradient f y) g ≤ dist (gradient f y) g' + dist g' g := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by rw [dist_comm g' g]; linarith
      _ = ε := by ring

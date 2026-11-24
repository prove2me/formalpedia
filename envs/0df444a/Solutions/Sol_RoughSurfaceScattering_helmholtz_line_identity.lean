-- Prove2me | solution 1 for RoughSurfaceScattering.helmholtz_line_identity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:37:35.521594+00:00
-- url     : https://prove2.me/submissions/9f4241b4-0d07-42e9-8caf-ec0e2c0cc6e0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_helmholtz_analytic

open MeasureTheory
open RoughSurfaceScattering

lemma pt_line (t c : ℝ) : pt t c = t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) + pt 0 c := by
  ext i; fin_cases i <;> simp [pt]

theorem solution (k : ℝ) (G : Set R2) (hG : IsOpen G) (u1 u2 : R2 → ℂ)
    (h1 : ContDiffOn ℝ 2 u1 G) (h2 : ContDiffOn ℝ 2 u2 G)
    (hH1 : IsHelmholtzOn G k u1) (hH2 : IsHelmholtzOn G k u2)
    (c d : ℝ) (hd : 0 < d) (hline : ∀ t : ℝ, pt t c ∈ G)
    (hseg : ∀ x ∈ measSeg c d, u1 x = u2 x) :
    ∀ t : ℝ, u1 (pt t c) = u2 (pt t c) := by
  have ha := (helmholtz_analytic k G hG u1 h1 hH1).sub (helmholtz_analytic k G hG u2 h2 hH2)
  -- the line `t ↦ (t, c)` is affine, hence analytic
  have hγ : AnalyticOnNhd ℝ (fun t : ℝ => pt t c) Set.univ := by
    intro t _
    have : (fun t : ℝ => pt t c) =
        fun t => t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) + pt 0 c := by
      funext t; exact pt_line t c
    rw [this]
    exact (analyticAt_id.smul analyticAt_const).add analyticAt_const
  have hcomp : AnalyticOnNhd ℝ (fun t : ℝ => (u1 - u2) (pt t c)) Set.univ :=
    ha.comp hγ fun t _ => hline t
  -- it vanishes near `0`
  have hev : (fun t : ℝ => (u1 - u2) (pt t c)) =ᶠ[nhds 0] 0 := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds (0 : ℝ) hd) fun t ht => ?_
    have htd : |t| ≤ d := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht; exact ht.le
    have hmem : pt t c ∈ measSeg c d := ⟨by simp [pt], by simpa [pt] using htd⟩
    simp [hseg _ hmem]
  have hzero := hcomp.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ 0) hev
  intro t
  exact sub_eq_zero.mp (hzero (Set.mem_univ t))

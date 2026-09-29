-- Prove2me | solution 1 for SphericalGeometry.lipschitzWith_smul_greatCirclePath
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T07:31:22.207565+00:00
-- url     : https://prove2.me/submissions/c88ce922-53f4-47c1-a670-57b28b498488

import Definitions.Def_spherical_great_circle
import Theorems.Thm_SphericalGeometry_dist_greatCirclePath

open SphericalGeometry

universe u

theorem solution {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v1 v2 : E) (h1 : ‖v1‖ = 1) (h2 : ‖v2‖ = 1) (ho : inner ℝ v1 v2 = 0)
    (alpha L : ℝ) (halpha : 0 ≤ alpha) (hL : 0 ≤ L) :
    LipschitzWith (Real.toNNReal (L * alpha))
      (fun theta : ℝ => L • greatCirclePath v1 v2 (alpha * theta)) := by
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  have hchord := SphericalGeometry.dist_greatCirclePath v1 v2 h1 h2 ho
    (alpha * s) (alpha * t)
  have hscal : dist (L • greatCirclePath v1 v2 (alpha * s))
      (L • greatCirclePath v1 v2 (alpha * t))
      = L * dist (greatCirclePath v1 v2 (alpha * s)) (greatCirclePath v1 v2 (alpha * t)) := by
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hL,
      dist_eq_norm]
  have hsin : |Real.sin ((alpha * s - alpha * t) / 2)| ≤ |(alpha * s - alpha * t) / 2| :=
    Real.abs_sin_le_abs
  have habs : |(alpha * s - alpha * t) / 2| = alpha * |s - t| / 2 := by
    rw [show alpha * s - alpha * t = alpha * (s - t) by ring, abs_div, abs_mul,
      abs_of_nonneg halpha]
    norm_num
  rw [habs] at hsin
  rw [hscal, hchord, Real.coe_toNNReal _ (by positivity), Real.dist_eq]
  nlinarith [hsin, hL, halpha, abs_nonneg (s - t)]

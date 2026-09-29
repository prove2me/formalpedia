-- Prove2me | solution 1 for SphericalGeometry.lipschitzWith_greatCirclePath
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T07:19:03.759426+00:00
-- url     : https://prove2.me/submissions/a505b773-37b7-4ab9-af80-5628a096dfbe

import Definitions.Def_spherical_great_circle
import Theorems.Thm_SphericalGeometry_dist_greatCirclePath

open SphericalGeometry

universe u

theorem solution {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v1 v2 : E) (h1 : ‖v1‖ = 1) (h2 : ‖v2‖ = 1) (ho : inner ℝ v1 v2 = 0) :
    LipschitzWith 1 (greatCirclePath v1 v2) := by
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  rw [SphericalGeometry.dist_greatCirclePath v1 v2 h1 h2 ho s t]
  have hsin : |Real.sin ((s - t) / 2)| ≤ |(s - t) / 2| := Real.abs_sin_le_abs
  have habs : |(s - t) / 2| = |s - t| / 2 := by
    rw [abs_div]
    norm_num
  rw [habs] at hsin
  have hd : dist s t = |s - t| := Real.dist_eq s t
  rw [hd]
  push_cast
  linarith [hsin]

-- Prove2me | solution 1 for SphericalGeometry.inner_greatCirclePath
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T23:15:28.410729+00:00
-- url     : https://prove2.me/submissions/72fc2fef-2954-443d-94a7-3c50e709c0c9

import Definitions.Def_spherical_great_circle

open SphericalGeometry

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v1 v2 : E) (h1 : ‖v1‖ = 1) (h2 : ‖v2‖ = 1) (ho : inner ℝ v1 v2 = 0) (s t : ℝ) :
    inner ℝ (greatCirclePath v1 v2 s) (greatCirclePath v1 v2 t) = Real.cos (s - t) := by
  have hso : inner ℝ v2 v1 = (0:ℝ) := by rw [real_inner_comm]; exact ho
  simp only [greatCirclePath, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, h1, h2, ho, hso]
  rw [Real.cos_sub]
  ring

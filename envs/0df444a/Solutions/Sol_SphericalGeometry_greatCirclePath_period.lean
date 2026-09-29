-- Prove2me | solution 1 for SphericalGeometry.greatCirclePath_period
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T23:17:09.048621+00:00
-- url     : https://prove2.me/submissions/4eca2ded-d6fd-499e-929b-39f230fadf19

import Definitions.Def_spherical_great_circle
import Theorems.Thm_SphericalGeometry_inner_greatCirclePath
import Theorems.Thm_SphericalGeometry_norm_greatCirclePath

open SphericalGeometry

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v1 v2 : E) (h1 : ‖v1‖ = 1) (h2 : ‖v2‖ = 1) (ho : inner ℝ v1 v2 = 0) (T : ℝ)
    (hT : greatCirclePath v1 v2 T = greatCirclePath v1 v2 0) :
    ∃ n : ℤ, T = n * (2 * Real.pi) := by
  have h := SphericalGeometry.inner_greatCirclePath v1 v2 h1 h2 ho T 0
  rw [hT, sub_zero, real_inner_self_eq_norm_sq,
    SphericalGeometry.norm_greatCirclePath v1 v2 h1 h2 ho] at h
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff T).mp (by rw [← h]; norm_num)
  exact ⟨n, hn.symm⟩

-- Prove2me | solution 1 for SphericalGeometry.greatCirclePath_comp_linearIsometryEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T11:18:06.662407+00:00
-- url     : https://prove2.me/submissions/413810b2-d0f6-4bdf-8008-39b4422fd0c5

import Definitions.Def_spherical_great_circle

open SphericalGeometry

universe u

theorem solution {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w : E ≃ₗᵢ[ℝ] E) (v1 v2 : E) (s : ℝ) :
    w (greatCirclePath v1 v2 s) = greatCirclePath (w v1) (w v2) s := by
  simp only [greatCirclePath, map_add, map_smul]

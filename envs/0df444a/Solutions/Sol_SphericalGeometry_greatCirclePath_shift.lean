-- Prove2me | solution 1 for SphericalGeometry.greatCirclePath_shift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-28T03:13:03.650413+00:00
-- url     : https://prove2.me/submissions/d39316f6-f603-4278-914b-8097a5f07ac6

import Definitions.Def_spherical_great_circle

open SphericalGeometry

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v1 v2 : E) (c s : ℝ) :
    greatCirclePath v1 v2 (s + c)
      = greatCirclePath (Real.cos c • v1 + Real.sin c • v2)
          (-(Real.sin c) • v1 + Real.cos c • v2) s := by
  simp only [greatCirclePath, Real.cos_add, Real.sin_add]
  module

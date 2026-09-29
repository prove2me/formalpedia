-- Prove2me | solution 1 for SphericalGeometry.greatCirclePath_add
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T11:17:55.88643+00:00
-- url     : https://prove2.me/submissions/1c2cb64d-0361-4677-9be6-c2fcb2f528fd

import Definitions.Def_spherical_great_circle

open SphericalGeometry

universe u

theorem solution {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v1 v2 : E) (c s : ℝ) :
    greatCirclePath v1 v2 (s + c)
      = greatCirclePath (greatCirclePath v1 v2 c) (greatCirclePath v2 (-v1) c) s := by
  simp only [greatCirclePath, Real.cos_add, Real.sin_add, smul_add, smul_neg,
    smul_smul, sub_smul, add_smul]
  module

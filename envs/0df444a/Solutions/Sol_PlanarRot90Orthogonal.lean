-- Prove2me | solution 1 for PlanarRot90Orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T23:01:10.363986+00:00
-- url     : https://prove2.me/submissions/f3ac7990-62b9-4f00-b695-68d53eb72530

import Definitions.Def_PlanarRot90

open Classical
noncomputable section

-- [TABLET NODE: PlanarRot90Orthogonal]
theorem solution (d : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ d (PlanarRot90 d) = 0 := by
  dsimp [PlanarRot90]
  rw [PiLp.inner_apply]
  simp
  ring

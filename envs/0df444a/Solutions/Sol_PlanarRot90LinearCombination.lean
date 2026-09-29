-- Prove2me | solution 1 for PlanarRot90LinearCombination
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-28T02:44:58.230635+00:00
-- url     : https://prove2.me/submissions/2f23d616-f55e-40f4-9942-36b0231b161d

import Definitions.Def_PlanarRot90

open Classical
noncomputable section

-- [TABLET NODE: PlanarRot90LinearCombination]
theorem solution (u : EuclideanSpace ℝ (Fin 2)) (A B : ℝ) :
    PlanarRot90 (A • u + B • PlanarRot90 u) =
      (-B) • u + A • PlanarRot90 u := by
  apply PiLp.ext
  intro k
  fin_cases k
  · simp [PlanarRot90]
  · simp [PlanarRot90]
    ring

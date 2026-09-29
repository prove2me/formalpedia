-- Prove2me | solution 1 for PlanarRot90Norm
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T22:58:53.250499+00:00
-- url     : https://prove2.me/submissions/ecd106be-3567-43f4-ac0d-6603f3d9f4d3

import Definitions.Def_PlanarRot90

open Classical
noncomputable section

-- [TABLET NODE: PlanarRot90Norm]
theorem solution (d : EuclideanSpace ℝ (Fin 2)) :
    ‖PlanarRot90 d‖ = ‖d‖ := by
  dsimp [PlanarRot90]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp
  ring

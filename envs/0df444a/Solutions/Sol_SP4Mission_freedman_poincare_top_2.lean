-- Prove2me | solution 2 for SP4Mission.freedman_poincare_top
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-11T14:21:51.347081+00:00
-- url     : https://prove2.me/submissions/c3926c6a-3fce-4843-a2a1-d6565fc3661e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_SP4Sphere
import Theorems.Thm_SP4Mission_homotopy_4sphere_punctured_is_euclidean
import Theorems.Thm_SP4Mission_compactification_of_euclidean_is_sphere

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission

theorem solution
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] :
    Nonempty (ContinuousMap.HomotopyEquiv M S4) → Nonempty (M ≃ₜ S4) := by
  intro hM
  rcases SP4Mission.homotopy_4sphere_punctured_is_euclidean M hM with ⟨p, hp⟩
  exact SP4Mission.compactification_of_euclidean_is_sphere M p hp

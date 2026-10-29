-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_data__p2m_89f9508a_afd6_4065_9e12_3df1eadb7958_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:47:36.018443+00:00
-- url     : https://prove2.me/submissions/f6af2ff4-d606-4b67-ad9d-0e566bf1558e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_identity__p2m_346cbd2e_54dd_4cc1_8c07_090cbf4f0cd3_a1
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound__p2m_346cbd2e_54dd_4cc1_8c07_090cbf4f0cd3_a1
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hConnected : M.Connected) (hM : HasPlanarDrawingOn M) :
    ∃ f : ℕ, Fintype.card V + f = M.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * M.edgeSet.ncard := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_identity__p2m_346cbd2e_54dd_4cc1_8c07_090cbf4f0cd3_a1
      M hConnected hM
  have hEdges :=
    WilliamsonShmoys.planar_simple_edge_bound__p2m_346cbd2e_54dd_4cc1_8c07_090cbf4f0cd3_a1
      M hV hConnected hM
  refine ⟨f, hEuler, ?_⟩
  omega
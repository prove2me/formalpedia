-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_257de7f1_d94a_4116_b7e0_524ede699478_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:29:33.565402+00:00
-- url     : https://prove2.me/submissions/f058ae28-5a8d-4cb0-9616-6dfa91c231af
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_5897f64b_d93f_46d0_b145_4fa00606e1c1_a3
import Theorems.Thm_WilliamsonShmoys_exists_connected_triangulated_planar_graph__p2m_5897f64b_d93f_46d0_b145_4fa00606e1c1_a3

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected ∧
      M.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨hLargeBound, hSmallBound⟩ :=
    WilliamsonShmoys.planar_drawing_edge_bound__p2m_5897f64b_d93f_46d0_b145_4fa00606e1c1_a3
      M hplanar
  obtain ⟨H, hHplanar, hHconnected, hHlarge, hHsmall⟩ :=
    WilliamsonShmoys.exists_connected_triangulated_planar_graph__p2m_5897f64b_d93f_46d0_b145_4fa00606e1c1_a3
      (V := V)
  refine ⟨H, hHplanar, hHconnected, ?_⟩
  by_cases hn : 3 ≤ Fintype.card V
  · have hM : M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by omega
    exact hM.trans (hHlarge hn)
  · have hnSmall : Fintype.card V ≤ 2 := by omega
    exact (hSmallBound hnSmall).trans (hHsmall hnSmall)
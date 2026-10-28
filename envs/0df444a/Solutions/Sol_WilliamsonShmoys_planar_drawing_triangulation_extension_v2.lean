-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:47:56.946598+00:00
-- url     : https://prove2.me/submissions/409d6bff-3704-470d-b56f-ae6abb439da1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_triangulation_289ce3bb
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_triangulation_289ce3bb

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hN, hmax, hcard⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_triangulation_289ce3bb M hV hM
  have htri := WilliamsonShmoys.maximal_planar_edge_count_triangulation_289ce3bb N hV hN hmax
  exact ⟨N, hMN, hN, hcard, htri⟩
-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_8e19dc79_980c_4b90_a9e5_d9bf409450af_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:29:56.741047+00:00
-- url     : https://prove2.me/submissions/4c3a8cc0-be23-4d51-abdf-14756e4ff370
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_edge_count__p2m_3be79666_71db_45ff_88b4_e34036e94e74_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hDraw : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hDrawM, hCount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_edge_count__p2m_3be79666_71db_45ff_88b4_e34036e94e74_a1
      L hDraw hCard
  have hEq : M = L := hMax M hLM hDrawM
  subst M
  exact hCount
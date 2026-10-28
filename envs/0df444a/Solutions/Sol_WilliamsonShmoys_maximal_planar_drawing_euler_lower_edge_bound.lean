-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_euler_lower_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:24:38.469024+00:00
-- url     : https://prove2.me/submissions/c32183a0-0037-4580-b368-ad6df734af4e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_triangulation_edge_count
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ L : SimpleGraph V, G ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = G) :
    3 * Fintype.card V ≤ G.edgeSet.ncard + 6 := by
  obtain ⟨L, hGL, hL, hcount⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_with_triangulation_edge_count G hV hG
  have hEq : L = G := hmax L hGL hL
  rw [hEq] at hcount
  omega
-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_of_edgeMaximal_planar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:36:46.32924+00:00
-- url     : https://prove2.me/submissions/d2b89a35-c7fb-4c4b-a1ba-0733890efacc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_edge_count_93a36477_a46b_4b11_b4cb_7379952edbbc

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : forall M : SimpleGraph V,
      L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L) :
    3 * Fintype.card V <= L.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hMdrawing, hCount⟩ :=
    WilliamsonShmoys.planar_supergraph_triangulation_edge_count_93a36477_a46b_4b11_b4cb_7379952edbbc L hV hL
  have hML : M = L := hMax M hLM hMdrawing
  rw [hML] at hCount
  exact hCount.le
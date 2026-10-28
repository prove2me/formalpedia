-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_connected_ge3_c00979a8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:41:31.563418+00:00
-- url     : https://prove2.me/submissions/5b924de7-21cd-4c03-b80c-fc8a020ff9ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_planar_drawing_has_proper_drawable_supergraph

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ L : SimpleGraph V, H ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ H) :
    H.Connected := by
  by_contra hconn
  obtain ⟨L, hHL, hdrawL, hnotHL⟩ :=
    WilliamsonShmoys.disconnected_planar_drawing_has_proper_drawable_supergraph
      H hV hH hconn
  exact hnotHL (hmax L hHL hdrawL)

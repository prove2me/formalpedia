-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_connected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:11:26.32766+00:00
-- url     : https://prove2.me/submissions/b8930f84-e51c-4ec7-b236-acd7d28d6c25
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_drawable_strict_supergraph_of_not_connected

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : forall H : SimpleGraph V, G ≤ H ->
      WilliamsonShmoys.HasPlanarDrawingOn H -> H ≤ G)
    (hV : 3 <= Fintype.card V) :
    G.Connected := by
  by_contra hconn
  obtain ⟨H, hGH, hHdraw, hnotHG⟩ :=
    WilliamsonShmoys.exists_drawable_strict_supergraph_of_not_connected
      G hdraw hV hconn
  exact hnotHG (hmax H hGH hHdraw)
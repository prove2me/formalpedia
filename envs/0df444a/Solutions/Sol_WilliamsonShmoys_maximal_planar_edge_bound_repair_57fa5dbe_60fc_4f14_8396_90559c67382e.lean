-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound_repair_57fa5dbe_60fc_4f14_8396_90559c67382e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:01:27.295358+00:00
-- url     : https://prove2.me/submissions/247145ea-3f66-452b-b3aa-58999393b52a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_to_triangulation

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V,
      L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L) :
    3 * Fintype.card V <= L.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hMplanar, hMcount⟩ :=
    WilliamsonShmoys.planar_extension_to_triangulation L hV hL
  have hML : M = L := hmax M hLM hMplanar
  subst M
  exact hMcount
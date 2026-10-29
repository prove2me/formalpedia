-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_drawing_on_finite_type
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:26:07.107185+00:00
-- url     : https://prove2.me/submissions/59401278-dd76-4d7c-ad36-ec300c85c016

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_with_sharp_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V, L <= M ->
      WilliamsonShmoys.HasPlanarDrawingOn M -> M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hLM, hM, hcount⟩ :=
    WilliamsonShmoys.planar_extension_with_sharp_edge_count L hV hL
  rw [hmax M hLM hM] at hcount
  exact hcount
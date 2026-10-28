-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound_3daebd93
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:05:59.549212+00:00
-- url     : https://prove2.me/submissions/bff1d682-97c4-4506-88a6-9beafdae1e95
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_edge_bound
import Theorems.Thm_WilliamsonShmoys_planar_connect_components
set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨H, hKH, hH_connected, hH_planar, hcard⟩ :=
    WilliamsonShmoys.planar_connect_components K hK
  have hbound := WilliamsonShmoys.planar_connected_edge_bound H hV hH_connected hH_planar
  exact le_trans hcard hbound
-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_face_degree_bound_b74a49f4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:49:44.894462+00:00
-- url     : https://prove2.me/submissions/95c89a41-d9ca-4b23-99fe-53599b4a619c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound_b74a49f4

set_option autoImplicit false

 theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hConnected : K.Connected) (hCard : 3 ≤ Fintype.card V)
    (f : ℕ) (hEuler : Fintype.card V + f = K.edgeSet.ncard + 2) :
    3 * f ≤ 2 * K.edgeSet.ncard := by
  have hEdge := WilliamsonShmoys.planar_simple_edge_bound_b74a49f4 K hK hCard
  omega
-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_edge_bound_b74a49f4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T07:09:34.045494+00:00
-- url     : https://prove2.me/submissions/49e2aa8c-aad5-4a56-b7aa-3d122f15e6cd

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_b74a49f4

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hKH, hH, hEdges, hEuler⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_b74a49f4 K hK hCard
  omega
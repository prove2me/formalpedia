-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound_repair_20261026
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:14:06.379448+00:00
-- url     : https://prove2.me/submissions/381bcb68-c307-4500-a497-5d5cb000dd3c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_edge_bound_20261026

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hKH, hHplanar, hEdgeCount, hHmax⟩ :=
    WilliamsonShmoys.planar_maximal_extension K hV hK
  have hBound :=
    WilliamsonShmoys.maximal_planar_euler_edge_bound_20261026 H hV hHplanar hHmax
  omega
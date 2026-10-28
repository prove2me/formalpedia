-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:15:52.594289+00:00
-- url     : https://prove2.me/submissions/ca244450-36ae-4278-bb9f-39d28e30f0e0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_maximal_extension_552f0216_da27_4340_ada6_5c47a5b50119
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_maximal_euler_bound_552f0216_da27_4340_ada6_5c47a5b50119

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hKH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_edge_count_upper_maximal_extension_552f0216_da27_4340_ada6_5c47a5b50119 K hK
  have hmono : K.edgeSet.ncard <= H.edgeSet.ncard :=
    Set.ncard_mono (SimpleGraph.edgeSet_mono hKH)
  have hbound :=
    WilliamsonShmoys.planar_edge_count_upper_maximal_euler_bound_552f0216_da27_4340_ada6_5c47a5b50119 H hH hcard hmax
  omega
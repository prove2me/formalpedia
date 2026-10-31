-- Prove2me | solution 2 for WilliamsonShmoys.planar_graph_edge_count_upper_bound__p2m_429266ef_2658_4bcb_86f5_df3246663c92_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:47:14.651986+00:00
-- url     : https://prove2.me/submissions/89cc11bb-43b5-417b-8223-31a259ba8ab1

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound_retry3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (Z : SimpleGraph V) (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) (hV : 3 ≤ Fintype.card V) : Z.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_edge_count_bound_retry3 Z hZ hV

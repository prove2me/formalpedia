-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_4c578d9c_5ad8_4ad5_bf9f_68265b93ec4b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:31:34.712646+00:00
-- url     : https://prove2.me/submissions/d41ca3a4-ef42-4ee9-82d0-8f57dca171f4

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound K hK hV

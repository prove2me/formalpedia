-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_graph_edge_count_upper__p2m_401bb865_eb7f_4687_8488_019108bab1f9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:41:38.154239+00:00
-- url     : https://prove2.me/submissions/69a61bf7-63c8-4492-be78-3b0e7ffc4f01

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_maximal_planar_extension__p2m_ad02c9e2_6f74_49a1_ae0d_05fd18f8b6b9_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_upper__p2m_ad02c9e2_6f74_49a1_ae0d_05fd18f8b6b9_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    N.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  let hExt :=
    WilliamsonShmoys.planar_graph_has_maximal_planar_extension__p2m_ad02c9e2_6f74_49a1_ae0d_05fd18f8b6b9_a1
      N hN
  let H := Classical.choose hExt
  have hSpec := Classical.choose_spec hExt
  have hNH : N <= H := hSpec.1
  have hH : WilliamsonShmoys.HasPlanarDrawingOn H := hSpec.2.1
  have hmax := hSpec.2.2
  have hHbound :=
    WilliamsonShmoys.maximal_planar_graph_edge_count_upper__p2m_ad02c9e2_6f74_49a1_ae0d_05fd18f8b6b9_a1
      H hH hmax hcard
  have hsub : N.edgeSet.ncard <= H.edgeSet.ncard :=
    Set.ncard_mono (SimpleGraph.edgeSet_mono hNH)
  omega
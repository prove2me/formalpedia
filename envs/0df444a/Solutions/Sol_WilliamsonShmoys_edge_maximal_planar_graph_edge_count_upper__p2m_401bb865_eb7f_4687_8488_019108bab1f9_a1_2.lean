-- Prove2me | solution 2 for WilliamsonShmoys.edge_maximal_planar_graph_edge_count_upper__p2m_401bb865_eb7f_4687_8488_019108bab1f9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:17:19.965849+00:00
-- url     : https://prove2.me/submissions/309c4b0b-25d5-4ad1-bcbe-55db3ac082f7

import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_ec05fb32_d087_4cea_a2cd_8a3ca91ed513

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    N.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_upper_bound_ec05fb32_d087_4cea_a2cd_8a3ca91ed513 N hcard hN

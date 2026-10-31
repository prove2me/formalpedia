-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_ff749fca_dc51_4e6e_b241_1d544557ca96_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:28:05.663879+00:00
-- url     : https://prove2.me/submissions/d74f0920-2d18-4cb3-9316-7d9ad47000eb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_upper_bound__p2m_429266ef_2658_4bcb_86f5_df3246663c92_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_lower_bound__p2m_429266ef_2658_4bcb_86f5_df3246663c92_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V) (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ W : SimpleGraph V, Z ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W = Z) :
    Z.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hu := WilliamsonShmoys.planar_graph_edge_count_upper_bound__p2m_429266ef_2658_4bcb_86f5_df3246663c92_a1 Z hZ hV
  have hl := WilliamsonShmoys.maximal_planar_graph_edge_count_lower_bound__p2m_429266ef_2658_4bcb_86f5_df3246663c92_a1 Z hZ hV hmax
  omega
-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_96b612ce_7021_404c_8189_06955c76f0dc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:14:49.997059+00:00
-- url     : https://prove2.me/submissions/7d3965f7-19b0-484f-a52c-86a0a755e117

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_sparse_graph_has_drawable_strict_extension__p2m_19289cd0_8bc0_4354_9e78_5126f5795da0_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M = L)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  by_contra hBound
  have hSparse : L.edgeSet.ncard + 6 < 3 * Fintype.card V := by omega
  obtain ⟨M, hLM, hML, hM⟩ :=
    WilliamsonShmoys.planar_sparse_graph_has_drawable_strict_extension__p2m_19289cd0_8bc0_4354_9e78_5126f5795da0_a2
      L hL hCard hSparse
  exact hML (hMax M hLM hM)
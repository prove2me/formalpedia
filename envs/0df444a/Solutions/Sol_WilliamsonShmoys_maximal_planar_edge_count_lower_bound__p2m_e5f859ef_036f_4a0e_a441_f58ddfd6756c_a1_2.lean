-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_e5f859ef_036f_4a0e_a441_f58ddfd6756c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:39:43.905205+00:00
-- url     : https://prove2.me/submissions/ea7fc389-6a3d-428d-98ec-66c0c2f61bfd

import Theorems.Thm_WilliamsonShmoys_edge_bound_of_inclusion_maximal_drawing

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet = L.edgeSet) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 :=
  WilliamsonShmoys.edge_bound_of_inclusion_maximal_drawing L hV hDraw hmax

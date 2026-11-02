-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_7bdfbc7b_3903_44da_a815_425149078ac6_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:17:34.345683+00:00
-- url     : https://prove2.me/submissions/6d54a46e-6526-4882-bf87-20afd5c8b93e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_supergraph__p2m_c3950eb8_41cb_4e65_a38c_065736da1c7d_a5
import Theorems.Thm_WilliamsonShmoys_triangulated_supergraph_edge_bound__p2m_c3950eb8_41cb_4e65_a38c_065736da1c7d_a5
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeFinset.card + 6 <= 3 * Fintype.card V := by
  obtain ⟨K, hKdec, f, hsub, hle, heuler, hfaces⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulated_supergraph__p2m_c3950eb8_41cb_4e65_a38c_065736da1c7d_a5
      H hcard hH
  letI : DecidableRel K.Adj := hKdec
  exact WilliamsonShmoys.triangulated_supergraph_edge_bound__p2m_c3950eb8_41cb_4e65_a38c_065736da1c7d_a5
    H hcard K f hsub hle heuler hfaces
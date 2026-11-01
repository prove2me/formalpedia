-- Prove2me | solution 2 for WilliamsonShmoys.planar_extension_edge_count__p2m_33d20c1e_677c_47dc_9e82_8d3a28e57fca_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:21:51.619206+00:00
-- url     : https://prove2.me/submissions/ffdae661-f483-44ac-8c06-372451d49cba

import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_exists_maximal_planar_supergraph
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planarDrawingOn_exists_maximal_planar_supergraph M hcard hM

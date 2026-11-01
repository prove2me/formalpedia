-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_extends_to_triangulation__p2m_1011a2ca_0dda_4069_a6bc_e4d75ecb3269_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:26:28.277453+00:00
-- url     : https://prove2.me/submissions/1b85e4a3-0fa3-4da8-83dd-c1a23dbfd4dc

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension__p2m_affb71eb_e232_4b0d_805e_31ff149cd3a9_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_affb71eb_e232_4b0d_805e_31ff149cd3a9_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  classical
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_affb71eb_e232_4b0d_805e_31ff149cd3a9_a1
      K hcard hK
  have hcount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_affb71eb_e232_4b0d_805e_31ff149cd3a9_a1
      L hcard hL hmax
  exact ⟨L, hKL, hL, hcount⟩
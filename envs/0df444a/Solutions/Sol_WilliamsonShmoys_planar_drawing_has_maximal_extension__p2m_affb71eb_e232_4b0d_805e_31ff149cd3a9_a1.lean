-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_affb71eb_e232_4b0d_805e_31ff149cd3a9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:30:50.184213+00:00
-- url     : https://prove2.me/submissions/49b8bc40-0d84-4960-9a1a-fbbddd9cf1f7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_simple_graph_type__p2m_d8eb9faa_7b6a_47f8_9dee_d4b2e8065d3d_a1
import Theorems.Thm_WilliamsonShmoys_simpleGraph_edgeSet_injective__p2m_d8eb9faa_7b6a_47f8_9dee_d4b2e8065d3d_a1
import Theorems.Thm_exists_maximal_superset_on_finite_type__p2m_d8eb9faa_7b6a_47f8_9dee_d4b2e8065d3d_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L.edgeSet ⊆ M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet = L.edgeSet := by
  classical
  haveI : Finite (SimpleGraph V) :=
    WilliamsonShmoys.finite_simple_graph_type__p2m_d8eb9faa_7b6a_47f8_9dee_d4b2e8065d3d_a1
  letI : Fintype (SimpleGraph V) :=
    Fintype.ofFinite (SimpleGraph V)
  obtain ⟨L, hKL, hL, hmax⟩ :=
    exists_maximal_superset_on_finite_type__p2m_d8eb9faa_7b6a_47f8_9dee_d4b2e8065d3d_a1
      (edge := fun G : SimpleGraph V => G.edgeSet)
      (P := WilliamsonShmoys.HasPlanarDrawingOn)
      (A := K)
      WilliamsonShmoys.simpleGraph_edgeSet_injective__p2m_d8eb9faa_7b6a_47f8_9dee_d4b2e8065d3d_a1
      hK
  exact ⟨L, hKL, hL, hmax⟩
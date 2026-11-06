-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_edge_maximal_supergraph__p2m_60f46665_7c74_42d7_b1ac_33e75a012818_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:28:13.474738+00:00
-- url     : https://prove2.me/submissions/707fdb54-e755-4c16-a247-6098d242f4e8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_FiniteSimpleGraph_exists_edge_maximal_extension__p2m_a584cd68_9d17_4361_8b29_312b20e50fca_a1
import Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_mono__p2m_a584cd68_9d17_4361_8b29_312b20e50fca_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      (∀ M : SimpleGraph V, L.edgeSet ⊆ M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M → M.edgeSet = L.edgeSet) := by
  have hdown : ∀ G H : SimpleGraph V, H.edgeSet ⊆ G.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn G → WilliamsonShmoys.HasPlanarDrawingOn H := by
    intro G H hsub hG
    exact WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_a584cd68_9d17_4361_8b29_312b20e50fca_a1 hsub hG
  obtain ⟨L, hKL, hL, hmax⟩ :=
    FiniteSimpleGraph.exists_edge_maximal_extension__p2m_a584cd68_9d17_4361_8b29_312b20e50fca_a1
      WilliamsonShmoys.HasPlanarDrawingOn hdown K hK
  exact ⟨L, hKL, hL, hmax⟩
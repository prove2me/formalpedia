-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion__p2m_31190146_93e5_4043_a404_538cf81f5878_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:26:43.081946+00:00
-- url     : https://prove2.me/submissions/3d818596-3b69-4737-9e0c-719523f9be59
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension__p2m_9bfda91a_9bda_408b_a2fd_6ab368fb7e28_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_9bfda91a_9bda_408b_a2fd_6ab368fb7e28_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn L) :
    ∃ K : SimpleGraph V, L.edgeSet ⊆ K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hLK, hKplanar, hKmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_9bfda91a_9bda_408b_a2fd_6ab368fb7e28_a1
      L hcard hplanar
  exact ⟨K, hLK, hKplanar,
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_9bfda91a_9bda_408b_a2fd_6ab368fb7e28_a1
      K hcard hKplanar hKmax⟩
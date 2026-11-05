-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_supergraph__p2m_a5768c2e_2608_4566_9f99_2d604f38d755_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:04:49.69452+00:00
-- url     : https://prove2.me/submissions/7365c45d-db0a-4df6-acda-d0382bb42fde

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_15067ae2_6164_4683_8340_3852ef322251_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_15067ae2_6164_4683_8340_3852ef322251_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    Exists fun K : SimpleGraph V =>
      And (WilliamsonShmoys.HasPlanarDrawingOn K)
        (And (N <= K)
          (K.edgeSet.ncard + 6 = 3 * Fintype.card V)) := by
  obtain ⟨K, hK, hNK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_15067ae2_6164_4683_8340_3852ef322251_a1
      N hplanar
  exact ⟨K, hK, hNK,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_15067ae2_6164_4683_8340_3852ef322251_a1
      K hK hmax hcard⟩
-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulating_extension__p2m_dafc8434_c658_484f_b8e8_b76293ec5b82_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:08:23.721611+00:00
-- url     : https://prove2.me/submissions/ab86e485-7825-4e3c-bfbe-0f7d788cf403

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_maximal_planar_extension__p2m_7b77c23b_62df_4ae5_b586_caedc2314578_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_7b77c23b_62df_4ae5_b586_caedc2314578_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hsub, hKplanar, hmax⟩ :=
    WilliamsonShmoys.planar_graph_has_maximal_planar_extension__p2m_7b77c23b_62df_4ae5_b586_caedc2314578_a1
      H hplanar
  exact ⟨K, hsub, hKplanar,
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_7b77c23b_62df_4ae5_b586_caedc2314578_a1
      K hKplanar hcard hmax⟩
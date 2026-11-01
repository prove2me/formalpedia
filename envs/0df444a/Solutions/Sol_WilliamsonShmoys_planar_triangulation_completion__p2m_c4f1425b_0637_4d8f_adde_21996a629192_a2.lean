-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_c4f1425b_0637_4d8f_adde_21996a629192_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:33:57.89546+00:00
-- url     : https://prove2.me/submissions/2c9d5b1c-3f72-4e55-a196-4b647dfa3fad

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal__p2m_4f728ae5_300b_4f49_98db_5976840980d8_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_4f728ae5_300b_4f49_98db_5976840980d8_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hKplanar, hKmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal__p2m_4f728ae5_300b_4f49_98db_5976840980d8_a1
      H hplanar hcard
  refine ⟨K, hHK, hKplanar, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_4f728ae5_300b_4f49_98db_5976840980d8_a1
    K hKplanar hcard hKmax
-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_exact_edge_count__p2m_00590216_3bdf_4c63_b52e_9e355ea90f1e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:19:13.241083+00:00
-- url     : https://prove2.me/submissions/b9fa46ad-393e-4fa6-aa41-99d4000d4ea3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_dbf7c19f_18a9_4ddb_bdc9_64443a6c5a07_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_dbf7c19f_18a9_4ddb_bdc9_64443a6c5a07_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      LE.le K L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        3 * Fintype.card V - 6 = L.edgeSet.ncard := by
  obtain ⟨L, hKL, hLplanar, hLmax⟩ :=
    WilliamsonShmoys.maximal_planar_extension__p2m_dbf7c19f_18a9_4ddb_bdc9_64443a6c5a07_a1
      K hKplanar
  exact ⟨L, hKL, hLplanar,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_dbf7c19f_18a9_4ddb_bdc9_64443a6c5a07_a1
      L hLplanar hV hLmax⟩